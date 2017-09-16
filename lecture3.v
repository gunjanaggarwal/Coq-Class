(** The mysteries of equality, SearchAbout, and induction... *)
Require Import Arith.

(** The symbol "=" is just infix notation for the identifier [eq]. *)
Locate "_ = _".
Check eq.
Check @eq.
(** And when we print out the definition of [eq]: *)
Print eq.
(**
  We see something like this:  

    Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x

  What's going on here? The definition says [eq] is parameterized by a type [A]
  and a value [x:A], and returns a predicate on [A] values (i.e., [A -> Prop]).  
*)
Check @eq nat 3.
Check @eq nat 3 4.
(**
  So for instance, [3 = 4] is short-hand for [@eq nat 3 4] and this is
  a [Prop].  Obviously, this [3 = 4] is something that we should not
  be able to prove.  

  Now the only way to prove an equality (i.e., construct a proof of [eq])
  is to use the data constructor [eq_refl].  Let's check [eq_refl]'s type:
*)
Check @eq_refl.
(**
  So [eq_refl] requires us to pass in a type [A] and a value [x:A] and
  returns a proof that [x = x].  So we can only seem to construct proofs
  of equality for the same object.  For instance:
*)
Check eq_refl 3.
(**
  Okay, so we managed to construct a proof that [3 = 3].  How do we
  prove [x = y] where [x] and [y] aren't exactly the same term?  
  For instance, we ought to be able to prove that [1+2 = 3].  

  Let's try this using tactics:
*)
Lemma one_plus_two_equals_three : 1 + 2 = 3.
Proof.
  apply eq_refl.
Qed.

Print eq.

Check eq_rect.
Definition eq_rect := 
fun (A : Type) (x : A) (P : forall _ : A, Type)
  (f : P x) (y : A) (e : @eq A x y) =>
(match e:(eq x y) in (eq _ z) return (P z) with
| eq_refl => f:(P x)
end):(P y).

(**
   What proof term did we actually construct?  Let's print it out
   and see...
*)
Print one_plus_two_equals_three.
(**
  This is confusing, but it's hard to see what's going on because Coq is not
  printing out all of the implicit arguments.  We can rectify this by writing:
*)
Set Printing All.
(**
  This just tells Coq we want to see all of the implicit arguments,
  and to turn off the notation. 
*)
Print one_plus_two_equals_three.

(** 
  So now we see that Coq is claiming that [@eq_refl nat (S (S (S 0)))]
  is an object that has type [@eq nat (plus (S 0) (S (S 0))) (S (S (S 0)))].

  Or, using notation, we are claiming that [@eq_refl nat 3] is an object
  that has type [1+2 = 3] which is just notation for [@eq nat (1 + 2) 3].

  When Coq is type-checking, it knows from the definition of [eq] that
  [@eq_refl nat 3] has type [3 = 3], but this is not the same as 
  [1+2 = 3], at least syntactically.  That is, Coq will try to compare
  [3 = 3] and [1+2 = 3] to see if they are the same.  Since they are
  not, it will try to simplify these types.  In particular, it will
  simplify [1+2] into [3], and then it is obvious that they are the same.

  Another way to say this is that Coq doesn't see any difference between
  [1 + 2] and [3] when it is type-checking.  We say that these two terms
  are _definitionally equal_.  In general, if we have two terms [M] and
  [N], and if [M] reduces to [P] and [N] reduces to [P], then Coq 
  considers [M] and [N] to be definitionally equal.

  What do we mean by reduce?  We'll talk about this more later, but
  informally, to reduce a term, Coq will:

  a) inline definitions of functions (such as +)

  b) beta-reduce: substitute an actual argument for a formal one, such 
     as reducing [(fun x => 1 + x) 2] to [1 + 2].

  c) match-reduce: reduce a pattern match on a known constructor.
     For instance, [match S 0 with | 0 => M | S x => N] will 
     reduce to [N[0/x]] (N with 0 substituted for x).

  d) unroll a recursive function [fix] if it needs to, but only
     if the unrolling will lead to a match reduction.

  So that's why as far as Coq is concerned [1 + 2] is the same thing
  as [3].  Similarly, we can prove:
*)
Lemma L1 : ((fun x => match x with | None => 0 | Some y => 1 + y end) (Some 2)) = 3.
  reflexivity.  (** Note that [reflexivity] is a tactic that is the same as [apply eq_refl]. *)
Qed.

Unset Printing All.  (** Turn fancy printing back on. *)

(** 
   How about proving something like this though, which should obviously 
   be true, but where the terms are not the same?
*)
Lemma eq_symmetric : forall (x y:nat), x = y -> y = x.
Proof.
  intros x y H.
  rewrite H.
  Show Proof.
  (** When [H : x = y], then [rewrite H] substitutes [x] for [y] in the goal.
     In contrast, [rewrite <- H] substitutes y for x in the goal.  And 
     [rewrite H in H'] substitutes x for y in the hypothesis H'. *)
  reflexivity.
Qed.

(** How is [rewrite] achieving the goal?  That is, what proof term do we
   get out?  We'll see in a second, but we can actually prove something
   more generic such as this:
*)
Lemma leibniz : forall {A:Type} (x y:A), 
                  (x = y) ->
                  forall (P : A -> Prop), P x -> P y.
Proof.
  intros A x y H P.
  rewrite H.
  intro a.
  apply a.
  (**auto.*)
  Show Proof.
Qed.

(** In English, what [leibniz] says is that whenever we have two
   [eq] terms [x] and [y], then for any proposition [P], such that
   [P] holds on [x], we can prove [P] holds on [y].  

   Given [leibniz], it's now easy to prove something like 
   [eq_symmetric] without using our magic [rewrite] tactic:
*)
Lemma eq_symmetric' : forall (x y:nat), x = y -> y = x.
Proof.
  intros x y H.
  Check (leibniz x y H (fun x' => x' = x)).
  Show Proof.
  (** Notice that when we choose [P] to be [fun x' => x' = x], then this
     this specializes [leibniz] to have type:
       [(fun x => x' = x) x -> (fun x' => x' = x) y]
     which if we simplify, is the same as:
       [x = x -> y = x]
     In short, [leibniz x y H (fun x' => x' = x) : x = x -> y = x]
     So if we apply this to our goal [y = x]:
   *)
  apply (leibniz x y H (fun x' => x' = x)).
  Show Proof.
   (** Then we are left proving [x = x]: *)
  reflexivity.
Qed.

(**
   As the name suggests, [leibniz] shows that Coq respects 
   substitution of [eq]-related terms in an arbitrary
   proposition.  And that's exactly what we would expect out of
   a notion of equality -- we can substitute equal terms without
   changing whether something is true or not.

   But still, how do we prove something like [leibniz] without
   using a magic tactic like [rewrite]?  The answer is a little
   complicated but boils down to the fact that when we do 
   a [match] on a proof that [x = y], then we know that the only
   way to construct such a proof is an [eq_refl] and hence,
   [y] must be [x]!  

   Now the way this is captured in Coq is not very intuitive.
   Let us take a look at this particular term which is automatically
   generated when we defined the [eq] Inductive type:
*)
Print leibniz.
Print eq.
Print eq_ind_r.
Print eq_ind.
Check eq_rect.
(**
  eq_rect 
     : forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, x = y -> P y

  The term [eq_rect] has a type very similar to [leibniz].  It says
  that for any type [A], any value [x:A], and any proposition [P] over
  [A] values, if [P] holds on [x], then for any [y:A], such that [x=y],
  then [P] holds on [y].  This is just a re-ordering of the assumptions
  we had in [leibniz] and indeed, we can use it to prove [leibniz]:
*)
Lemma leibniz' : forall {A:Type} (x y:A), 
                  (x = y) ->
                  forall (P : A -> Prop), P x -> P y.
Proof.
  intros A x y H P H1.
  Check eq_rect.
  apply (@eq_rect A x P H1 y H).
Qed.

(** But now what does [eq_rect] look like?  *)
Print eq_rect.

(** eq_rect = 
     fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
       match e in (_ = y0) return (P y0) with
       | eq_refl => f
       end

   So [eq_rect] does a pattern match on the proof [e] that [x = y].  The
   form of the [match] specifies two additional clauses that we haven't
   seen before, an [in (_ = y0)] clause and a [return (P y0)] clause.

   The [in (_ = y0)] is a pattern that is meant to match the type of
   [e].  In this case, since [e]'s type is [x = y], the pattern variable
   [y0] is bound to [y].  The [return (P y0)] clause specifies what
   we intend the match to return as a function of the information we
   learn about [y0].  Now the only way that we can build a proof of
   an equality is using [eq_refl] and it only builds proofs of the 
   form [x = x].  So when we match on [e], we have effectively discovered
   that [y0] must be [x].  And thus the return type should be [P x], 
   after we substitute [x] for [y0] in the [return] clause.  But this
   is exactly what [f]'s type is!  

   Stepping back, what all of this mechanism lets you do is exactly
   what Leibniz equality requires:  subsitute equal terms for equal
   terms.  Critical to this is the fact that we can only build a proof
   of equality using [eq_refl] and it only allows us to prove the
   same object is equal to itself.  

   TL;DR:  rewrite isn't magic.  It's just doing a fancy pattern match.
   Now to be honest, I can never remember how to write these fancy
   patterns.  So I usually just use tactics, such as [rewrite], to
   build the code for me.  
*)

(** Okay, so let's prove a few more things using [rewrite] *)
Lemma eq_trans : forall {A:Type} (x y z:A), x = y -> y = z -> x = z.
Proof.
  intros A x y z H1 H2.
  rewrite <- H2.
  apply H1.
Qed.

(** Here's a surprising lemma... *)
Lemma one_plus : forall (x:nat), x + 1 = S x.
Proof.
  intro x.
  simpl.  (** Oops!  This doesn't seem to simplify things... *)
  unfold plus.  (** unfolds the definition of [plus] *)
  (** Aha!  We can't make progress with this.  So how to proceed? *)
  fold plus.  (** fold back the definition of [plus] *)

(** If we could prove that [x + 1 = 1 + x] then maybe we can make
   progress.  Perhaps there's a library lemma that already establishes
   the fact that [add] is commutative?  
*)
  SearchAbout (?a + _ = _ + ?a).
(** The [SearchAbout] command takes a meta-level pattern and tries to
   find any definitions in scope whose type matches that pattern.  
   Here, the [?a] and [?b] are pattern variables which can match
   any term.  Notice that the pattern captures just what we are looking
   for -- some term that is a proof that "+" is commutative.  
   And indeed, there are two such proofs, one called [plus_comm]
   and one called [NPeano.Nat.add_comm].  

   You might play around with SearchAbout to see what other goodies
   are just lying around.  Certainly, you don't want to reprove
   things that you don't have to.  
*)
  SearchAbout (_ + _).  (** Whoa!  That's a long list of things... *)
  SearchAbout (?a * (?b + ?c) = _).  (** Aha! Distributivity! *)
  SearchAbout (?a + (?b + ?c) = (?a + ?b) + ?c).  (** Aha! Associativity! *)
(**
  The libraries have lots and lots of stuff.  I can never remember
  their names.  SearchAbout is wonderful.

  Anyway, we can rewrite using [plus_comm] to simplify our goal:
*)
   rewrite Nat.add_comm.
   (** rewrite plus_comm. *)
(** Did this improve our situation?  Let's unfold [plus] and see: *)
   simpl.  (** yes!  Now the match can reduce and it does.  *)
   reflexivity.
Qed.

(** But how do we prove something like [plus] is commutative or associative?  *)
Check plus_comm.
Print plus_comm.
Print Nat.add_comm.
Check plus_assoc.
Print plus_assoc.
Print Nat.add_assoc.
Print Nat.bi_induction.
(** Aha!  They are using a function called [nat_ind]: *)
Check nat_ind.

(**   nat_ind
       : forall P : nat -> Prop,
           P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n

  In English, [nat_ind] takes some proposition [P] over numbers,
  asks us to provie a proof that [P] holds on [0], and a proof
  that for any [n], whenever [P n] holds, then [P] holds on the
  successor of [n].  If we manage to do that, then we can prove
  that [P] holds on all numbers.  This is quite literally the
  natural number induction we are taught when we do paper-and-
  pencil proofs.  

  So let's use [nat_ind] to construct a proof that [plus] is 
  associative.
*)


Lemma plus_associative : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  apply (nat_ind (fun n => forall m p, n + (m + p) = (n + m) + p)).
    (** base case:  n = 0 *)
    simpl.
    reflexivity.
  intros n IH m p.
  simpl.
  rename m into m'.
  rename p into p'.
  rewrite IH.
  reflexivity.
Qed.
(** 
   Actually, there's a tactic that will take care of doing
   the first step for you. It's called (surprise) [induction]:
*)
Lemma plus_associative' : forall p m n, n + (m + p) = (n + m) + p.
Proof.
  induction n.
  * simpl. (** base case *)
    auto.
  * simpl. (** inductive case *)
    rewrite IHn.
    auto.
Qed.
(**
   The [induction] tactic looks at the goal's type (in this case a universal
   over a [nat]), and uses that to find the appropriate [???_ind] function,
   in this case [nat_ind], and then applies that for you.  

   But what does [nat_ind] look like? 
*)
Print nat_ind.
Print nat_rect.
(** [nat_ind] is defined in terms of [nat_rect].  The only difference is that
   [nat_rect] works with an arbitrary type, whereas [nat_ind] only works for
   establishing propositions.  That is, the type of [nat_rect] looks the same
   as [nat_ind] except instead of [P] being restricted to a predicate over
   [nat]s, it can be any [Type] over [nat]s (including [Prop]s).  

   The definition of [nat_rect] looks like this:
*)
Fixpoint my_nat_rect{P: nat -> Type} (base : P 0) (IH : forall n, P n -> P (S n))(n:nat) :=
    match n as n0 return P n0 with
      | 0 => base 
      | S n0 => IH n0 (my_nat_rect base IH n0)
    end.
(** 
   It's just a frickin recursive function (!) where when [n] is 0, we return 
   the base case, and when [n] is [S n0], we call [my_nat_rect] recursively
   on [n0] to get a term of type [P n0] and then use the induction hypothesis
   [IH] to transform that to a term of type [P (S n0)].  

   Notice that the termination checker of Coq is crucial here, for establishing
   that no matter what [n] we pass it, we get out a proof for that [n].  That is,
   it's crucial, if we want to think of this as a proof for all natural numbers,
   that it doesn't diverge for some number.

   Now when you define an inductive definition, such as [nat], Coq will automatically
   generate three functions for you.  Let's try it:
*)
Inductive mynat : Type := 
| ZERO : mynat
| SUCC : mynat -> mynat.
(*
   mynat is defined
   mynat_rect is defined
   mynat_ind is defined
   mynat_rec is defined
*)
Check mynat_rect.
(** forall P:mynat->Type, P ZERO -> (forall m, P m -> P (SUCC m)) -> forall m, P m *)
Check mynat_ind.
(** forall P:mynat->Prop, P ZERO -> (forall m, P m -> P (SUCC m)) -> forall m, P m *)
Check mynat_rec.
(** forall P:mynat->Set, P ZERO -> (forall m, P m -> P (SUCC m)) -> forall m, P m *)

(** There's nothing magical about them, they are just there for convenience. 
   Try looking at some other Inductive's induction principles:
*)
Check bool_rect.
Check list_rect.
Print list_rect.
Check option_rect.
Print option_rect.
Print option.

Inductive tree(A:Type) : Type := 
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.

Check tree_rect.
Print tree_rect.

(** Problem Set 2 : Induction and Equality
Induction.
Next, we're going to exercise the simpl, induction and rewrite tactics. 
Replace the Admitted.'s with an appropriate proof. 
Don't forget to write Qed. to terminate your proofs. 
It goes without saying that you shouldn't just prove 
these by using a library lemma :-) 
However, if you get stuck proving one of these, then it is sometimes useful
to look for one that does solve this, using the top-level SearchAbout command,
and then Print the corresponding proof.
*)
Module PSET2_EX1.
  Require Import List.

  Lemma zero_plus_x : forall n, 0 + n = n.
  Proof.
    induction n.
    * simpl. reflexivity.
    * simpl. reflexivity.
  Qed.

  Lemma x_plus_zero : forall n, n + 0 = n.
  Proof.
    induction n.
    * simpl. reflexivity.
    * simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma x_plus_zero' : forall n, n + 0 = n.
  Proof.
    intro n.
    rewrite(Nat.add_comm n 0).
    apply (zero_plus_x n).
  Qed.

  Lemma map_map : forall {A B C:Type} (f:A->B) (g:B -> C) (xs:list A), 
    map g (map f xs) = map (fun x => g (f x)) xs.
  Proof.
    intros.
    Check map.
    (** map
     : forall A B : Type, (A -> B) -> list A -> list B 
    *)
    SearchAbout (map _ _ ).
    induction xs.
      *simpl. reflexivity.
      *simpl. rewrite IHxs. reflexivity.
  Qed.

  Lemma app_assoc : forall {A:Type} (xs ys zs:list A), 
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
  Proof.
  Print "++".
  intros.
  induction xs. 
  *simpl. reflexivity.
  *simpl. rewrite IHxs. reflexivity.
  Qed.

  Lemma map_is_fold : forall {A B} (f:A->B) (xs:list A),
    map f xs = fold_right (fun x y => (f x)::y) nil xs.
  Proof.
    intros.
    induction xs.
    * simpl. reflexivity.
    * simpl. rewrite IHxs. reflexivity.
  Qed.

  Definition list_sum (xs:list nat) : nat := fold_right plus 0 xs.

  Lemma list_sum_app : forall (t1 t2: list nat), 
     list_sum (t1 ++ t2) = list_sum t1 + list_sum t2.
  Proof.
    intros.
    induction t1.
    * simpl. reflexivity.
    * simpl. rewrite IHt1. apply (plus_assoc).
  Qed.

  Lemma nat_assoc: forall (a b c : nat), a + ( b + c) = a + b + c.
  Proof.
    intros a b c .
    induction a.
    * simpl. reflexivity.
    * simpl. rewrite IHa. reflexivity.
  Qed.

  Lemma list_sum_app' : forall (t1 t2: list nat), 
     list_sum (t1 ++ t2) = list_sum t1 + list_sum t2.
  Proof.
    intros.
    induction t1.
    * simpl. reflexivity.
    * simpl. rewrite IHt1. apply nat_assoc.
  Qed.

  Inductive tree(A:Type) : Type := 
    | Leaf : tree A
    | Node : tree A -> A -> tree A -> tree A.
  Implicit Arguments Leaf [A].
  Implicit Arguments Node [A].

  Fixpoint mirror{A:Type} (t:tree A) : tree A := 
    match t with
      | Leaf => Leaf
      | Node lft v rgt => Node (mirror rgt) v (mirror lft)
    end.

  (** Lemma mirror_tree: forall A (t:tree A), mirror t = t.
  Proof.
    intros.
    induction t.
    * simpl. reflexivity.
    * simpl. rewrite IHt1. rewrite IHt2.
  OH- Now I see this is not true.
  *)
  
  Lemma mirror_mirror : forall A (t:tree A), mirror (mirror t) = t.
  Proof.
    intros.
    induction t.
    * simpl. reflexivity. 
    * simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  Qed.

  Fixpoint flatten {A:Type} (t:tree A) : list A := 
    match t with 
      | Leaf => nil
      | Node lft v rgt => (flatten lft) ++ v::(flatten rgt)
    end.

  Fixpoint tree_sum (t:tree nat) : nat := 
    match t with 
      | Leaf => 0
      | Node lft v rgt => (tree_sum lft) + v + (tree_sum rgt)
    end.

   Lemma nat_assoc': forall (a b c d : nat), a+ b+c+d = a + (b+c+d).
   Proof.
    intros.
    induction a.
    * simpl. reflexivity.
    * simpl. rewrite IHa. reflexivity.
   Qed.

   Lemma list_sum_assoc: forall(l1: list nat) (a:nat) (l2: list nat),
    list_sum( l1) + a + list_sum(l2) = list_sum(l1 ++ a :: l2).
   Proof.
     intros.
     induction l1.
     * simpl. reflexivity.
     * simpl. rewrite (nat_assoc'). rewrite IHl1. reflexivity.
   Qed.

  Lemma tree_flatten_sum : forall t, tree_sum t = list_sum (flatten t).
  Proof.
    Print list_sum.
    (** list_sum = 
        fun xs : list nat => @fold_right nat nat Init.Nat.add 0 xs
             : list nat -> nat
    *)
    intros.
    induction t.
    *simpl. reflexivity.
    *simpl. rewrite IHt1. rewrite IHt2. apply list_sum_assoc.
  Qed.

SearchAbout (rev).

  Lemma rev_rev_list: forall (l1: list nat), rev(rev l1) = l1.
  Proof.
    intros.
    induction l1.
    * simpl. reflexivity.
    * simpl. (** @rev nat (@rev nat l1 ++ a :: @nil nat) = a :: l1 *)
     rewrite(rev_app_distr). simpl. rewrite IHl1. reflexivity.
  Qed.

  Lemma fstar: forall (l1 l2 : list nat), rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros.
    rewrite <- (rev_rev_list l1).
    rewrite H.
    rewrite (rev_rev_list).
    reflexivity.
  Qed.
  End PSET2_EX1.


Module PSET2_EX2.
(** 
Modeling.
Consider the following famous puzzle, taken from Raymond E. 
Smullyan's book, "What is the name of this book?".
Portia's suitor is asked to solve a following puzzle to prove his worth.
Her portrait is placed in one of three sealed caskets, gold, 
silver, and lead. Each casket has an inscription, but only one of the
 three inscriptions is true. The inscriptions read as follows:
Gold : "The portrait is in this casket" 
Silver : "The portrait is not in this casket" 
Lead : "The portrait is not in the gold casket"
Your task is to formalize the puzzle in Coq and prove the answer correct. 
hints: You can use a Variable declaration to introduce 
unknown variables and assumptions local to a section.
*)

Section SmullyanPuzzle.

(** Sections are a convenient way to develop theories 
that are universally quantified over some variables.
*)
Inductive chest : Type :=
  | Silver
  | Gold 
  | Lead.

(** Unlike an axiom, Variables are just universally 
quantified in the items in this section below that mention them. 
See the output of Check ItsSilver after the section is closed.
*)
Variable location : chest.

(** 
Replace this variable with a Definition.
Variable inChest: chest -> Prop.
*)

Definition inChest (c: chest) :  Prop:= location=c.


(**  Give a definition for the inscriptions on the chests.
*)
Definition inscription (c: chest): Prop :=
match c with 
|Gold => inChest c
|Silver => ~(inChest c)
|Lead => ~(inChest Gold)
end.

(** Capture the assumption that only one chest is truthful.
*)
Definition assumption : Prop :=
forall c1 c2, inscription c1 -> inscription c2 -> c1=c2.



Theorem ItsSilver : assumption -> inChest Silver.
Proof.
  intros. unfold inChest.
  remember location as ll. destruct ll.
  - reflexivity.
  - unfold assumption in H. apply H.
    * simpl. compute. rewrite Heqll. reflexivity.
    * simpl. compute. subst. intros. discriminate.
  -unfold assumption in H. apply H.
    * simpl. compute. subst. intros. discriminate.
    * simpl. compute. subst. intros. discriminate.
Qed.
(**
 simpl in *;  unfold inChest; auto.
    subst. congruence.
    apply (f_equal (fun c => match c with Gold => True | _ => False end)) in Heq.
    rewrite <- Heq. exact I. exact
unfold inChest. unfold assumption in H. inversion H.
*)
End SmullyanPuzzle.
Check assumption.