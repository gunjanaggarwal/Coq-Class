Require Import List CpdtTactics Omega.
Import ListNotations.

(* An abbreviation which given two nats n and m, 
   decides whether {n <= m} or {n > m}. *)
Definition nat_lte := Compare_dec.le_gt_dec.

Locate "+".
Print sumbool.
Print or.


(* Insert a number into a list.  Assumes the list is
   sorted in in non-decreasing order. *)
Fixpoint insert (n:nat) (xs:list nat) : list nat := 
  match xs with 
    | [] => [n]
    | h::t => if nat_lte n h then n::h::t else h::(insert n t)
  end.

Fixpoint insert_to_listG (xs : list nat) (xy : list nat) : list nat :=
  match xs with
  | [] => xy
  | h :: t => insert_to_listG t (insert h xy) 
end. 

Definition insert_sortG (xs : list nat) : list nat :=
  insert_to_listG xs [].

Eval compute in insert_sortG [3;2;5;1;7].

(* Insertion sort. *)
Definition insert_sort (xs:list nat) : list nat := 
  fold_right insert [] xs.

(* Simple test. *)
Eval compute in insert_sort [3;2;5;1;7].

(* A useful predicate on lists.  list_all P xs holds 
   when P holds on each element of xs. *)
Definition list_all {A:Type} (P:A->Prop) (xs:list A) : Prop := 
  fold_right (fun h t => P h /\ t) True xs.

(* We can use list_all to define a notion of a sorted list. *)
Fixpoint sorted (xs:list nat) : Prop := 
  match xs with 
    | [] => True
    | h::t => sorted t /\ list_all (le h) t
  end.

(* Notice that this produces a predicate (which we can't prove!) *)
Eval compute in sorted [3;1;2].

(* We can prove this predicate though. *)
Example sorted_123 : sorted [1;2;3].
Proof.
  simpl. 
  auto 100.
Qed.

(* Here's an alternative definition of sorted using an
   couple of inductive definitions. *)
Inductive list_lte : nat -> list nat -> Prop := 
| nil_list_lte : forall n, list_lte n nil
| cons_list_lte : forall n h t, n <= h -> list_lte n t -> list_lte n (h::t).

Inductive sorted' : list nat -> Prop := 
| nil_is_sorted : sorted' nil
| cons_is_sorted : forall h t, list_lte h t -> sorted' t -> sorted' (h::t).

Hint Constructors sorted' list_lte.

(* And here's an example proof that the list [1;2;3] is sorted'. *)
Example sorted'_123 : sorted' [1;2;3].
Proof.
auto 100.
Qed.

Locate "<->".
Print iff.
Ltac myinv H:= inversion H; subst; simpl in *; clear H.

Ltac dands :=
repeat match goal with
[H: _ /\ _ |- _] =>
  let Hl := fresh H "l" in
  let Hr := fresh H "r" in
  destruct H as [Hl Hr]
end.

Ltac dandsIff := unfold iff in *; dands.

(* The two definitions of sorted'ness are equivalent. *)
Lemma list_lte_iff_list_all_lte : 
  forall n (xs:list nat), 
    list_lte n xs <-> list_all (le n) xs.
induction xs. 
- simpl. unfold iff. split; auto.
- auto. split.
  + intros. simpl. myinv H. split.
    * assumption.
    * rewrite <- IHxs. assumption.
  + intros. simpl in *. dands. rewrite <- IHxs in Hr. auto.
Qed.

Lemma sorted_iff_sorted' : 
  forall (xs:list nat), 
    sorted xs <-> sorted' xs.
induction xs.
* unfold iff. split; intros; simpl; auto.
* unfold iff. split.
  dandsIff.
  - intros. simpl in *. dands. apply list_lte_iff_list_all_lte in Hr. auto.
  - intros. simpl in *. myinv H. dandsIff. 
    apply list_lte_iff_list_all_lte in H2. auto.
Qed.

(* Let's try to prove that insert_sort produces a sorted list. *)
Lemma insert_sort_sorted : forall xs, sorted (insert_sort xs).
Proof.
  induction xs ; crush.
  unfold sorted.
  (* We're stuck since Coq doesn't know if (insert a (insert_sort xs))
     is empty or a cons. Let's try to convince it. *)
  remember (insert a (insert_sort xs)) as sorted_xs.
  destruct sorted_xs.
  (* If (insert a (insert_sort xs)) is empty, we don't have to prove
     anything -- an empty list is already sorted.  (But of course,
     (insert a (insert_sort xs)) is not empty. *)
  auto.
  (* Ugh!  We're no better off than we were before. Let's abort... *)
  Abort.

(* What we need to do first is prove something useful about 
   insert.  For example, if xs is sorted and we insert n into
   it, we should get back a sorted list.  Before juming into
   that, let me define some useful lemmas. *)

(* A useful lemma that lifts implication to list_all.  It says
   that if P x -> Q x for any x, then list_all P xs -> list_all Q xs.
*)
Lemma list_all_imp{A}: 
  forall (P Q : A -> Prop),
    (forall (x:A), P x -> Q x) -> 
  (forall (xs:list A), list_all P xs -> list_all Q xs).
Proof.
  intros P Q H.
  induction xs.
  - simpl. auto.
  - simpl. intros. dands. apply H in H0l. auto.
Qed.


(* If n <= m and m <= each element of xs, then n <= each element of xs. *)
Lemma list_lte_nm (n m:nat) (xs:list nat) : 
  n <= m -> list_all (le m) xs -> list_all (le n) xs.
Proof.
  intros.
  (* Aha!  Now we can use the list_all_imp lemma to avoid
    reasining about the list, and reduce this to a single element. *)
  eapply (list_all_imp (le m) (le n)) ; [ intros ; omega | auto ].
Qed.

(* So let's try to prove this fact now... *)
Lemma insert_sorted : forall n xs, sorted xs -> sorted (insert n xs).
Proof.
  induction xs;  crush.
  destruct (nat_lte n a) ; simpl.
  crush.
  (* Here's where our lemma above comes into play. *)
  eapply list_lte_nm ; eauto.
  crush.
  (* Ugh!  How are we supposed to prove that a <= insert n xs?
     Intuitively it's true, but how can we show this?  We need
     to know that if we insert n into xs, then the elements of
     the resulting list are either equal to n or one of the xs. *)
  Abort.

(* An equivalent way to capture "list_all" *)
Lemma in_list_all {A} (P:A->Prop) (xs:list A) : 
  (forall x, In x xs -> P x) <-> list_all P xs.
Proof.
  induction xs ; crush.
Qed.

(* Now we can prove that if you insert n into xs, then
   any element of the resulting list is either equal to
   n or one of the xs. *)
Lemma in_insert :
  forall (xs:list nat) (n:nat), 
    forall x, In x (insert n xs) -> x = n \/ In x xs.
Proof.
  induction xs ; crush. simpl in *.
  destruct (nat_lte n a) ; crush.
  specialize (IHxs _ _ H0). crush.
Qed.

(* The opposite fact will also be useful. *)
Lemma insert_in : 
  forall (xs:list nat) (n:nat), 
    forall x, x = n \/ In x xs -> In x (insert n xs).
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; crush.
  destruct (nat_lte n x) ; crush.
  destruct (nat_lte n a) ; crush.
Qed.

Lemma insert_sorted : forall n xs, sorted xs -> sorted (insert n xs).
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; simpl.
  crush.
  eapply list_lte_nm ; eauto.
  crush.
  (* here's where in_list_all comes into play -- we turn the
     list_all into reasoning about a particular element in 
     (insert n xs) which has to be either n or one of the xs. *)
  apply in_list_all.
  intros.
  generalize (in_insert xs n x H2). intro.
  destruct H3.
  crush.
  (* here's where the opposite lemma comes into play. *)
  rewrite <- in_list_all in H1.
  crush.
Qed.

(* Once we've proved that insert produces a sorted list, we
   can easily prove that insert_sort produces a sorted list. *)
Lemma insert_sort_sorted : forall xs, sorted (insert_sort xs).
Proof.
  induction xs ; crush.
  apply insert_sorted ; auto.
Qed.

(* However, note that the following function also produces
   a sorted list:
*)
Definition bogus_sort (xs:list nat) : list nat := nil.

Lemma bogus_sort_sorted (xs:list nat) : sorted (bogus_sort xs).
  apply I.
Qed.

(* Here's an attempt to capture what it means for a sort
   function to actually be correct.   The output should
   be sorted, the length of the input should equal the
   length of the output, and every member of the input 
   should be in the output (and vice versa, though this
   can be shown given that the lengths are the same.)  Is
   this specification right?!?
*)
Definition sublist {A} (xs ys:list A) : Prop := 
  forall (x:A), In x xs -> In x ys.

Definition sort_corr (xs ys:list nat) : Prop := 
  sorted ys /\ sublist xs ys /\ length xs = length ys.

(* There are, of course, alternative definitions.  For
   instance, we might specify that the output is a sorted
   permutation of the input.  

   Often, you can't predict what will be the most useful
   specification.  That depends largely on who'se using
   the code and what they need to know.  For instance,
   we might be using the sort routine as part of a set
   implementation.  In that case, these properties would
   be good enough, though we'd probably want to build
   some derived properties.  For instance, we might 
   like to know that 

     (sort_corr xs ys) -> (sort_corr xs zs) -> ys = zs

   which can be proven from the spec above.  
*)

(* Let's prove now that our insertion sort is "correct",
   according to the definition we gave above.  We have
   already shown insert_sort produces a sorted list. 
   Now we just need to establish the other two properties: *)
Lemma insert_sort_sublist : forall xs, sublist xs (insert_sort xs).
Proof.
  unfold sublist.
  induction xs ; crush ; apply insert_in ; crush.
Qed.

Lemma insert_length : forall xs n, length (insert n xs) = S (length xs).
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; crush.
Qed.

Lemma insert_sort_length : forall xs, length xs = length (insert_sort xs).
Proof.
  induction xs ; crush.
  rewrite insert_length. auto.
Qed.

(* And finally, we can show insertion sort is correct. *)
Lemma insert_sort_corr : forall xs, sort_corr xs (insert_sort xs).
Proof.
  unfold sort_corr. intro.
  split. 
  apply insert_sort_sorted.
  split.
  apply insert_sort_sublist.
  apply insert_sort_length.
Qed.

Definition injection_fun (f: nat-> nat): Prop :=
forall (x y : nat), f x = f y -> x = y.

Definition Permutation' (xs ys : list nat) (f: nat -> nat) : Prop :=
   injection_fun f /\  forall i, nth_error xs i = nth_error ys (f i) 
   .

Definition Permutation (xs ys: list nat): Prop :=
  length xs = length ys /\ exists f, Permutation' xs ys f.


Definition sort_corr' (xs ys:list nat) : Prop := 
  sorted ys /\ Permutation xs ys.

Lemma nth_error_list_append: forall (a: nat) (xs: list nat), 
    forall n, nth_error xs n = nth_error (a :: xs) (S n).
Proof.
    intros. reflexivity.
Qed. 

Lemma Insert_indices: forall (a: nat)(xs: list nat), 
  exists n, 
  nth_error (insert a xs) n = Some a
  /\ (forall n1, n1 < n -> nth_error xs n1 = nth_error (insert a xs) n1)
  /\ ( forall n2, n2 >= n -> 
            nth_error xs n2 = nth_error (insert a xs) (S n2)).
Proof.
  induction xs.
    * simpl. exists 0. split; firstorder.
    * Print ex. destruct IHxs. simpl. destruct (nat_lte a a0).
      - exists 0. simpl. crush.
      - exists (S x). simpl. dands. split; auto; split.
         + intros. destruct n1; crush.
         + intros. destruct n2; crush.
Defined.

Arguments ex_intro {A} {P} x p.
Eval vm_compute in (Insert_indices 9 [0;1;2;5;2;100]). 
Print ex.

Lemma Permutation'_corr: forall (a : nat) (xs sxs : list nat),
length xs = length sxs ->
forall f : nat -> nat,
Permutation' xs sxs f ->
exists f0 : nat -> nat, 
Permutation' (a :: xs) (insert a sxs) f0.
Proof.
intros. unfold Permutation' in *.
destruct (Insert_indices a sxs) as [ai p].
set ( ff := fun x => 
          match x with 
          | 0 => ai 
          | S n' => if lt_dec (f n') ai  
          then (f n') else S (f n')
          end ).
exists ff. split.
* subst ff. unfold injection_fun. intros x y Heq.
 destruct x,y;auto.
  + destruct (lt_dec (f y) ai); crush.
  + destruct (lt_dec (f x) ai); crush.
  + destruct (lt_dec (f y) ai), (lt_dec (f x) ai); crush.
* intros. destruct i; try (crush; fail).
  simpl.
  destruct (lt_dec (f i) ai);  try (crush; fail). 
Qed.

(**intros.
unfold Permutation' in *. dands. revert dependent xs. 
revert dependent f.
  induction sxs as [| hsxs txsx Hind].
  - intros. simpl in *. destruct xs; simpl in *; try discriminate. 
     exists (fun x => x). crush.
  - intros. simpl in *.
    destruct (nat_lte a hsxs).
    + clear Hind. 
      set (ff := fun i => match i with 
                        |0 => 0
                        |S i' => S(f i')
                         end).
      exists ff. split.
      * subst ff. intros x y Heq. destruct x, y; crush.
      * intros. destruct i; simpl in *; crush.
   + rename xs into xso. destruct xso as [| xsoh  xsot]; simpl in *; try discriminate.
      myinv H. specialize (Hind xsot H1). destruct Hind as [ff Hind].
        * intros. specialize (H0r (S i)). simpl in *. rewrite H0r.
 eexists. split.
      Focus 2.
**)


Lemma insert_sort_corr' : forall xs, sort_corr' xs (insert_sort xs).
Proof.
unfold sort_corr'.
intros.
split. apply insert_sort_sorted.
unfold Permutation. induction xs;
 [simpl; split; auto; exists (fun x => x); split; crush|].
 dands. destruct IHxsr as [f IHxsr].
  unfold insert_sort. simpl. fold (insert_sort xs).
  remember (insert_sort xs) as sxs. clear Heqsxs.
  rewrite insert_length. split; auto.
  eapply Permutation'_corr; eauto.
Qed.

(********************************************************)

(* Of course, we don't want to use an O(n^2) sort in practice.
   So here, I develop a merge sort.  This shows off something
   new -- defining a recursive function using something besides
   structural induction to establish termination.
*)


(* First, we need to define a function to merge two (already
   sorted lists).  Now normally, we'd write this as:

   Fixpoint merge (xs ys:list nat) {struct xs} : list nat := 
      match xs, ys with 
      | [], ys => ys
      | xs, [] => xs
      | h1::t1, h2::t2 => if nat_lte h1 h2 then 
                           h1 :: (merge t1 ys)
                         else
                           h2 :: (merge xs t2)
      end.

   But unfortunately, Coq will reject this because it's
   not the case that xs is always getting smaller, nor
   the case that ys is always getting smaller.  Of course,
   *one* of them is always getting smaller, so eventually,
   this will terminate.  

   But in this case, we can hack around the problem by
   simply re-organizing the function as follows:
*)


Definition merge_inner_merge (mm : list nat -> list nat) x xs:=
(fix inner_mergeg  (ys : list nat) : list nat :=
          match ys with
          | [] => x :: xs
          | y :: ys' =>
              if nat_lte x y
              then x :: (mm ys)
              else y :: inner_mergeg ys'
          end).

Fixpoint merge (xs:list nat) : list nat -> list nat := 
  match xs with 
    | nil => fun ys => ys
    | (x::xs') => fun ys => merge_inner_merge (merge xs') x xs' ys
  end.

Recursive Extraction merge.

Fixpoint merge' (xs:list nat) : list nat -> list nat := 
  match xs with 
    | nil => fun ys => ys
    | (x::xs') => 
      (fix inner_merge (ys:list nat) : list nat := 
         match ys with 
           | nil => x::xs'
           | y::ys' => if nat_lte x y then 
                         x :: (merge xs' (y::ys'))
                       else 
                         y :: (inner_merge ys')
         end)
  end.

(* Note that for the out loop, we only call it with a
   smaller xs, and for the inner loop, we only call it
   with a smaller ys.  So Coq can see by structural
   induction the loops that the definition terminates.

   Note that if you tried to pull inner_merge out and
   define it as a top-level function, Coq would no 
   longer be able to tell that merge terminates.  
   In this sense, Coq's termination checking isn't
   modular.
*)

(* Test that merge works. *)
Eval compute in merge [1;3;5] [2;4;6].
Eval compute in merge [3] [1;4].

(* This function takes a list of lists of nats, and 
   merges each pair of lists.  See the example below. *)
Fixpoint merge_pairs (xs:list (list nat)) : list (list nat) := 
  match xs with 
    | h1::h2::t => (merge h1 h2) :: (merge_pairs t)
    | xs' => xs'
  end.

Eval compute in merge_pairs [[1;3];[2;4;9];[0];[2;3]].
Eval compute in merge_pairs [[1;3];[2;4;9];[0]].

(* To define our actualy merge sort, we want to take the
   initial list [n1;n2;...;nm] and turn it into a list of 
   singleton lists: [[n1];[n2];...;[nm]] and then successively
   call merge_pairs until we get a single list out. *)

(* This function takes a list and turns it into a list
   of singleton lists of the elements. *)
Definition make_lists (xs:list nat) : list (list nat) := 
  List.map (fun x => x::nil) xs.

Eval compute in make_lists [5; 1; 4; 2; 3].
Eval compute in merge_pairs (merge_pairs (merge_pairs (make_lists [5; 1; 4; 2; 3]))).
(* As with merge, I would like to write the following function
   which is intended to iterate merging the pairs of a list of
   lists until we get a single list out:

  Fixpoint merge_iter (xs:list (list nat)) : list nat := 
    match xs with 
    | [] => []
    | [h] => h
    | h1::h2::xs' => merge_iter (merge_pairs (h1::h2::xs'))
    end.

  But Coq can't tell that this terminates.  The problem is
  that we are calling merge_iter on (merge_pairs (h1::h2::xs'))
  instead of xs'.  Since in principle, merge_pairs could return
  a list no smaller than the input, Coq rejects the definition.

  All is not lost, though.  In Coq, we can define functions
  that use an arbitrary measure (or really, any well-founded
  relation) and show that the measure is always decreasing
  to convince Coq the function terminates.  

  Before doing that, I need to establish a lemma that:

   length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs)

  This is a little tricky to prove since we are peeling off
  2 elements instead of one.  One way to prove it is using
  so-called "strong-induction", but here's another way:
*)
Lemma merge_pairs_length' : 
  forall xs, (forall h1 h2, 
                length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs)) /\
             (forall h, 
                length (merge_pairs (h::xs)) <= length (h::xs)).
Proof.
  induction xs ; crush.
Qed.

(* What I did in merge_pairs_length' is generalize my desired
   property to one that holds regardless of the number of elements
   in the list.  Try doing it without the second case and see what
   goes wrong... *)

(* Anyway, my decreasing measure is now easy to establish from the
   lemma above. *)
Lemma merge_pairs_length : 
  forall h1 h2 xs, length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs).
Proof.
  intros.
  specialize (merge_pairs_length' xs). 
  intros [H _].
  apply H.
Qed.

(* Now I'm going to define my merge_iter function.  Since it's
   not structurally recursive, but rather, defined using a measure,
   I first need to import a couple of libraries. *)
Require Import Program.
Require Import Wf.

(* The [Function] construct is similar to the [Fixpoint]
   construct.  The big difference is that I'm required to state
   a [{measure ...}] clause to convince Coq as to what's going
   down.  In this case, the length of the argument list is always
   going down when we do a recursive call.
 *)
Require Import Recdef.
Function merge_iter (xs: list (list nat)) { measure length xs } : list nat :=
  match xs with 
    | nil => nil
    | h::nil => h
    | h1::h2::xs' => merge_iter (merge_pairs (h1::h2::xs'))
  end.
(* Notice that Coq spits out a bunch of stuff here and says
   there's 1 obligation remaining.  This obligation arises
   as a result of the recursive call -- we need to show that
   the measure is actually decreasing.  The command [Next Obligation]
   let's us provide a proof of the needed fact.  Note that
   until we finish the proofs of all obligations, the 
   function [merge_iter] is not defined. *)
intros. apply (merge_pairs_length).
Defined.
  
(* Alternatively, you can use [Program Fixpoint], but this doesn't generate all of
   the same useful features. 
*)
Program Fixpoint
  merge_iter' (xs : list (list nat)) {measure (length xs)} : list nat :=
  match xs with 
    | nil => nil
    | h::nil => h
    | h1::h2::xs' => merge_iter' (merge_pairs (h1::h2::xs'))
  end.
Next Obligation.
  apply (merge_pairs_length h1 h2 xs'). 
Qed.

Print merge_iter.

(* If we print out merge_iter... *)
Print merge_iter.
Print merge_iter_terminate.
(* ...we see that the [Function] did a lot of work for us
   to translate our definition into the real core of Coq.  It's
   using a special function Fix_sub, along with some other hidden
   definitions that you can print out if you like. *)
Print Fix_F_sub.
(* Fix_F_sub is defined to be:

   fun (A : Type) (R : A -> A -> Prop) (P : A -> Type)
     (F_sub : forall x : A, (forall y : {y : A | R y x}, P (` y)) -> P x) =>
       fix Fix_F_sub (x : A) (r : Acc R x) {struct r} : P x :=
       F_sub x

  If you look carefully, this is proceeding by (structural) induction
  on r and is just a seemingly infinite loop.  But since r must be
  getting smaller each time around the loop, the loop actually
  terminates.

  What is r?  It's a proof that the value x is "accessible" (Acc) with
  respect to the relation R.  In our case, R is essentially the 
  relation between the length of the original input
  the length of the list we are recursing on (a < relation on the
  lengths of the lists.)  The "accessible" notion is capturing the
  idea that our relation has no infinite descending chains.  In the
  case of <, there is a least element, namely 0.  So if we are always
  going down in the relation, we will eventually get to 0.  

  TL;DR:  You don't need to understand all of this.  You just need
  to be able to use the [Function ... {measure ...}] construct
  to write functions and argue that the generated obligations are
  met (i.e., that your measure really is decreasing.)
*)

(* Once we've defined our merge_iter, we can finally define
   our merge_sort: *)
Definition merge_sort (xs:list nat) := 
  merge_iter (make_lists xs).

(* Let's test that it's working... *)
Eval compute in merge_sort [7;8;3;5;1;2;6;4].
Eval compute in merge_sort [3;2;7;8].

(* Exercises:

1. Show that

   a. sorted xs -> sorted ys -> sorted (merge xs ys)
   b. (length xs + length ys) = length (merge xs ys)
   c. In x xs \/ In x ys <-> In (merge xs ys)

2. Show that 

   a. list_all sorted xs -> list_all sorted (merge_pairs xs)
   b. (sum of lengths of lists in xs) = 
        (sum of lengths of lists in merge_pairs xs)
   c. (x is in one of the lists in xs) <->
        (x is in one of the lists in merge_pairs xs)

3. Show that

   a. list_all sorted xs -> sorted (merge_iter xs)
   b. (sum of lengths of lists in xs) = length of (merge_iter xs)
   c. (x is in one of the lists in xs) <-> In x (merge_iter xs)

4.  Show that

    a. make_lists xs is sorted
    b. In x xs <-> (x is in one of the lists in make_lists xs)
    c. length xs = (sum of the lengths of the lists in make_lists xs)

5.  Show that sort_corr xs (merge_sort xs)

*)


Lemma insert_smallest_result_is_sorted: forall (xs: list nat) (a:nat),
sorted xs -> list_all (le a) xs -> sorted (a::xs).
Proof.
Print sorted.
intros.
remember (a::xs) as xs'.
destruct xs'; crush.
Qed.


Lemma first_elem_isless: forall (xs: list nat) (a: nat),
 sorted (a::xs) -> list_all (le a) (a::xs).
Proof.
crush.
Qed.


Print merge.

Lemma or_remove_mid {A B C}: A  \/ C -> A \/  B \/ C.
tauto.
Qed.


Lemma inBetterDestruct 
  {A:Type} (eqdec : forall a b:A, {a=b}+{a<>b}) (x h:A) tl:
  In x (h::tl) -> x=h \/ (x<>h /\ In x tl).
Proof using.
  intros Hin.
  simpl in *.
  destruct (eqdec x h); firstorder.
Qed.

(*
Lemma elem_eitherin_xs_or_ys': forall (xs ys : list nat) mm (x a : nat),
  (forall b h tl, In b (mm tl) -> In b (mm (h::tl)))
  -> In a (merge_inner_merge mm x xs ys) -> In a (x::xs) \/ In a ys.
Proof.
intros.
induction ys as [| y ys Hind].
- simpl in *. auto.
- simpl in *. remember (nat_lte x y). destruct s.
  * firstorder.
  * rename H0 into Hin.
    apply inBetterDestruct in Hin;[| apply Nat.eq_dec].
    destruct Hin;[firstorder|]. dands.
    apply or_remove_mid.
    apply Hind in H0r; auto. crush.
    right. apply H.
Qed.
*)

(*
Lemma elem_eitherin_xs_or_ys': forall (xs ys : list nat) mm (x a : nat),
(In a (mm ys) -> In a xs \/ In a ys) ->
  In a (merge_inner_merge mm x xs ys) -> In a (x::xs) \/ In a ys.
Proof.
intros.
induction ys as [| y ys Hind].
- simpl in *. auto.
- simpl in *. remember (nat_lte x y). destruct s.
  * firstorder.
  * apply inBetterDestruct in H0;[| apply Nat.eq_dec].
    destruct H0;[firstorder|]. dands.
    apply or_remove_mid.
    apply Hind; auto. crush.
Qed.

Lemma elem_eitherin_xs_or_ys': forall (xs ys mm : list nat) (x a : nat),
(forall b, In b mm -> In b xs \/ In b ys) ->
  In a (merge_inner_merge mm x xs ys) -> In a (x::xs) \/ In a ys.
Proof.
intros.
induction ys as [| y ys Hind].
- simpl in *. auto.
- simpl in *. remember (nat_lte x y). destruct s.
  * crush . apply H in H1. crush.
  * simpl in *. 
    destruct (Nat.eq_dec y a);[crush|].
    destruct H0; [crush|].
    apply or_remove_mid.
    apply Hind; auto.
    
    crush.
apply Hind in H1; crush.
    Focus 2.
    apply H in H2.

Abort.
*)

Lemma elem_eitherin_xs_or_ys: forall (xs ys : list nat) (a: nat),
  In a (merge xs ys) -> In a xs \/ In a ys.
Proof.
intro xs.
induction xs as [| x xs Hind].
- intros. simpl in *. auto.
- intros. simpl in *.
induction ys as [| y ys Hindy].
+ simpl in *. auto.
+ simpl in *. remember (nat_lte x y). destruct s.
  simpl in *.
  * destruct H; [crush; fail |]. apply Hind in H. crush.
  * apply inBetterDestruct in H;[| apply Nat.eq_dec].
    destruct H;[crush; fail|]. dands.
    apply or_remove_mid.
    apply Hindy; auto. 
Qed.
(*
  pose proof (XX H).
  apply XX in H.
  simpl in *.
Check (eq_refl:
((fix inner_merge (ys : list nat) : list nat :=
          match ys with
          | [] => a :: xs
          | y :: ys' =>
              if nat_lte a y then a :: merge xs ys else y :: inner_merge ys'
          end) =
(fix inner_mergeg (ys : list nat) : list nat :=
           match ys with
           | [] => a :: xs
           | y :: ys' =>
               if nat_lte a y then a :: merge xs ys else y :: inner_mergeg ys'
           end))

).

  apply XX in H.

Check (@In nat a0
    ((fix inner_merge (ys : list nat) : list nat :=
        match ys return (list nat) with
        | nil => @cons nat a xs
        | cons y ys' =>
            match nat_lte a y return (list nat) with
            | left _ => @cons nat a (merge xs ys)
            | right _ => @cons nat y (inner_merge ys')
            end
        end) ys)).

  apply XX in H.

 destruct ys.
 + crush.
 + remember (nat_lte a0 n). destruct (nat_lte a0 n); crush.

   remember ((fix inner_merge (ys : list nat) : list nat :=
           match ys with
           | [] => a0 :: xs
           | y :: ys' =>
               if nat_lte a0 y
               then a0 :: merge xs (y :: ys')
               else y :: inner_merge ys'
           end)) as inner_merge_fn.
   induction ys.
    * crush.
    *
*)


Lemma add_smallest_element: forall (xs ys : list nat) (a: nat),
    list_all (le a) (xs) -> 
    list_all (le a) (ys) ->  list_all (le a) (merge xs ys).
Proof.
  intros xs ys. remember ( merge xs ys).
  induction l.
  + crush.
  + subst. crush.
Abort.

Lemma merge_preserves_sorted : forall xs ys,
   sorted xs -> sorted ys -> sorted (merge xs ys).
Proof.
Print merge.
induction xs as [| x xs Hindx]; auto. intros ys.
induction ys as [| y ys Hindy]; auto.
intros.
pose proof (Hindx (y ::ys)).
simpl. crush. remember (nat_lte x y) as s.
  rewrite <- in_list_all in H3.
  rewrite <- in_list_all in H4.

 destruct s.
* crush. rewrite <- in_list_all. 
  intros ? Hin.
  apply elem_eitherin_xs_or_ys in Hin. simpl in *. crush.
* simpl in *. split;[crush|]. 
  change (merge_inner_merge (merge xs) x xs ys) 
    with (merge (x::xs) ys).
  rewrite <- in_list_all. intros. 
  apply elem_eitherin_xs_or_ys in H0.
  pose proof (H4 x0). pose proof (H3 x0). firstorder.
Qed.


Lemma merge_equal_inner_merge x xs ys :
(merge_inner_merge (merge xs) x xs ys)
= merge (x::xs) ys.
simpl.
reflexivity.
Qed.


Lemma merge_preserves_length : forall xs ys,
   (length xs + length ys) = length (merge xs ys).
Proof.
intro xs.
induction xs; simpl in *. auto.
simpl in *. induction ys; simpl in *; auto.
remember (nat_lte a a0) as s. destruct s.
- simpl in *. pose proof (IHxs (a0 ::ys)). rewrite <- H.
  simpl. reflexivity.
- simpl in *. rewrite <- IHys. auto.
Qed.

Lemma elem_eitherin_xs_or_ys': forall (xs ys : list nat) (a: nat),
  In a xs \/ In a ys -> In a (merge xs ys).
Proof.
intros xs. induction xs as [| x xs Hindx].
* intros. simpl in *. firstorder.
* intros ys. induction ys as [| y ys Hindy].
  - intros. simpl in *. firstorder.
  - intros. simpl in *. remember (nat_lte x y) as s. 
    destruct s.
    + pose proof (Hindx (y ::ys) a). simpl in *. tauto.
    + simpl in *. change (merge_inner_merge (merge xs) x xs ys) 
    with (merge (x::xs) ys).
    change (merge_inner_merge (merge xs) x xs ys) 
    with (merge (x::xs) ys) in Hindy.
    pose proof (Hindy a). tauto.
Qed.


Lemma merge_preserves_In : forall xs ys x,
   In x xs \/ In x ys <-> In x (merge xs ys).
Proof.
unfold iff. split.
- apply   elem_eitherin_xs_or_ys'.
- apply elem_eitherin_xs_or_ys.
Qed.

Require Import List.
Locate count.
Require Import NArith.
Require Import NPeano.
Definition count := count_occ Nat.eq_dec.

Lemma merge_preserves_count : forall (xs ys : list nat) x,
   count xs x + count ys x = count (merge xs ys) x.



