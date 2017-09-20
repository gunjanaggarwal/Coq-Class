(** Comments in Coq are as in Ocaml and SML:  they start with a left-paren 
   and asterisk, and are closed with an asterisk and right-paren. *)

Require Import Arith.

(** [Require Import Arith.] is a top-level command that tells Coq to import
   the definitions from the [Arith] library (arithmetic) and to make the
   definitions available at the top-level.  All top-level commands end
   with a period.
*)


Definition four : nat := 4.

(** A top-level definition begins with the keyword [Definition], followed
   by an identifier (in this case [four]) that we want to use, a colon,
   a type, [:=], and then an expression followed by a period.  
   Here the type of the number [4] is [nat] which stands for natural number.  *)

Definition four' := 2 + 2.
(** You can leave off the type information and Coq can often infer it.  
   But it can't always infer types, and it's good documentation to put
   the types on complicated definitions. *)

Eval compute in four'.

Eval compute in four + four'.
(** [Eval compute in <exp>.] lets you evaluate an expression to see the 
   resulting value and type. *)

Check four'.
(** [Check <exp>] lets you check the type of an expression. *)

Print four'.
(** [Print <identifier>] lets you see the definition of the identifier. *)

Definition four'' := (6 - 4) * 2.

Check four''.
Eval compute in four''.
Print four''.

Definition inc (x:nat) : nat := x + 1.
(** To define a function, we just make a parameterized definition.*)

Check inc.
Eval compute in inc.
Eval compute in inc four.

Definition inc' x := x + 1.
(** As in Ocaml, we can leave off the types and Coq can usually infer them,
   but not always. *)

Check inc'.
Print inc'.
Eval compute in inc' four.

Definition inc'' := fun (x:nat) => x + 1.
(** Parameterized definitions are just short-hand for a regular definition
   using a lambda expression. *)

Check inc''.
Eval compute in inc'' four.


Definition add1 x y := x + y.
Definition add2 (x:nat) (y:nat) := x + y.
Definition add3 (x y:nat) := x + y.
(** When the types are the same, we can group parameters as in [add']. *)
Definition add4 := fun x => fun y => x + y.
(** Multiple parameters are just iterated lambdas. *)

Check add1.
Check add2.
Check add3.
Check add4.
Eval compute in add1 5 4.
Eval compute in add2 5 4.

Definition inc''' := add1 1.
Eval compute in inc'''.
Eval compute in inc''' 4.

Inductive bool : Type := 
| true 
| false.
(** An inductive definition is just like an Ocaml datatype definition,
   though the syntax is a little different.  Here, we are defining
   a new [Type] called [bool] with constructors [true] and [false].
   Unlike Ocaml, we can (and generally need to) provide the type of 
   each data constructor, hence both [true] and [false] are defined
   as constructors that immediately return a [bool].  

   Notice that when we evaluate this definition, Coq says that not
   only is [bool] defined, but also [bool_rect], [bool_ind], and 
   [bool_rec].  We'll discuss those later on when we start talking
   about proving things.
*)
Check true.
Check false.
Print bool.

Definition negb (b:bool) : bool := 
  match b with 
    | true => false
    | false => true 
  end.
(** The definition above shows how we use pattern-matching to tear apart
   an inductive type, in this case a [bool].  The syntax is similar to 
   Ocaml except that we use "=>" for the guard instead of "->" and we
   have to put an "end" to terminate the "match". *)

Check negb.
Eval compute in negb true.
Eval compute in negb false.

Definition andb (b1 b2:bool) : bool := 
  match b1 with 
    | true => b2
    | false => false
  end.

Eval compute in andb true false.
Eval compute in andb true true.

Definition orb b1 b2 := 
  match b1 with
    | true => true
    | _ => b2
  end.

Eval compute in orb true false.
Eval compute in orb true true.

(** The [Arith] module defines this [nat] type already.  It is a way to
   represent the natural numbers, with a base case of zero, "0" and 
   successor constructor [S]. Notice that the type of [S] declares
   it to take a [nat] as an argument, before returning a [nat]. 

Inductive nat : Type := 
  | O : nat
  | S : nat -> nat.

type nat = O | S of nat
*)

Print nat.

(** 
   A digression:

   In informal math, we tend to think of a "type" as a set of
   objects.  For instance, we think of [nat] as the set of
   objects {0,1,2,3,...}.  But we can also form sets out of
   sets.  For instance, we can have {nat,bool,string}.  Technically,
   to avoid circularities, [nat] is considered a "small" set,
   and {nat,bool,string} is considered a "large" set, sometimes
   called a class.  Stratifying our sets is necessary to avoid
   constructions such as S = { s : set | s is not contained in s }
   (Russell's paradox.)  

   In Coq, the identifier [Set] refers to a universe of 
   types, including {nat,bool,string,...}.  So in some sense, 
   the identifier [Set] names a class of types.  We sometimes
   say that [Set] is the type of the collection 
   {nat,bool,string,...}. When we build 
   certain kinds of new types out of elements of [Set], then we 
   have to move up to a new universe.  Internally, that universe
   is called Type_1.  (Actually, [Set] is represented as Type_0
   internally.)  And if we build certain types out of Type_1,
   we have to move up to Type_2.  So Coq has an infinite hierarchy
   Set a.k.a. Type_0, Type_1, Type_2, ...   

   Now figuring out where in this hierarchy a definition should go
   isn't that hard, and in fact, Coq automagically infers this
   for you.  When you write [Type], you are really writing [Type_x]
   and Coq is later solving for [x] to make sure your definitions
   don't contain a circularity.  In fact, with the exception of
   [Set] and one more very special universe, [Prop], you can't
   even explicitly say at what level you want a given definition.
   
   For now, we can just ignore this and use [Type] everywhere.
*)
Check O.
Check 0.   (** the numeral 0 is just notation for the constructor O *)
Eval compute in 0.
Eval compute in 3.
Check S.
Check S 0. (** 1,2,3 are short-hand for (S O), (S (S O)) and (S (S (S O))). *)
Check S (S (S 0)).

Definition is_zero (n:nat) : bool := 
  match n with 
    | 0 => true
    | S _ => false
  end.

Fixpoint add'' (n m:nat) : nat := 
  match m with 
    | 0 => n
    | S m' => S (add'' n m')
  end.
(** We construct recursive functions by using the keyword "Fixpoint". *)

Eval compute in add'' 4 3.
Print add''.

Definition add5 :=
  fix local_add (n m:nat) : nat := 
  match n with 
    | 0 => m
    | S n' => S (local_add n' m)
  end.
(** Alternatively, we can use a "fix" expression which builds a recursive
   functions, similar to the way "fun" builds a non-recursive function.
*)

Eval compute in add5 4 3.
Print add5.

(** Pairs *)
Definition p1 : nat * nat := (3,4).  (** pair of nats *)
Definition p2 : nat * bool := (3, true).  (** nat and bool *)
Definition p3 : nat * bool * nat := (3,true,2).

Eval compute in add3 (fst p1) (snd p1).  
(** [fst] extracts the first component of a pair, and [snd]
   extracts the second component. *)

Eval compute in fst p3.
Eval compute in snd p3.

Print pair.
Eval compute in match p1 with 
                  | pair x y => x + y
                end.
Locate "_ * _".

(** Notice that [(3,true,2)] is really short-hand for [((3,true),2)]. 
   and [nat * bool * nat] is short for [(nat * bool) * nat]. *)

(** Options *)
Definition opt1 : option nat := None.
Definition opt2 : option nat := Some 4.
(** An [option t] is either [None] or [Some] applied to a value of type [t]. 
   Notice that unlike Ocaml, we write [option nat] instead of [nat option].
*)
Print option.

Fixpoint subtract (m n:nat) : option nat := 
  match m, n with 
    | _, 0 => Some m
    | 0, S _ => None
    | S m', S n' => subtract m' n'
  end.
Eval compute in subtract 5 2.
Eval compute in subtract 2 5.

Definition subt (m n:nat) : nat := 
  match subtract m n with 
    | None => 0
    | Some i => i
  end.
Eval compute in subt 5 2.
Eval compute in subt 2 5.

(** Sums *)
Locate "_ + _".
Print sum.

Definition s1 : nat + bool := inl 3.
Definition s2 : nat + bool := inr true.

Print s1.

(** We build something of type [t1 + t2] by using either [inl] or 
   [inr].  It's important to provide Coq enough type information
   that it can figure out what the other type is. *)

Definition add_nat_or_bool (s1 s2: nat + bool) : nat + bool := 
  match s1, s2 with 
    | inl n1, inl n2 => inl (n1 + n2)
    | inr b1, inr b2 => inr (orb b1 b2)
    | _, _ => inr false
  end.

(** Lists *)
Require Import List.
Print list.
Definition l1 : list nat := nil.
Definition l2 : list nat := 3::2::1::nil.
Definition l3 : list bool := true::false::nil.
Definition l4 : list (nat + bool) := (inl 3)::(inr true)::nil.

Fixpoint append (l1 l2:list nat) : list nat := 
  match l1 with 
    | nil => l2
    | h::t => h::(append t l2)
  end.

Eval compute in append l2 l2.

Fixpoint add_list (l1 l2:list nat) : option (list nat) := 
  match l1, l2 with 
    | nil, nil => Some nil
    | n1::l1, n2::l2 => 
      match add_list l1 l2 with
        | None => None
        | Some l => Some ((n1+n2)::l)
      end
    | _, _ => None
  end.

Eval compute in add_list l2 l2.
Eval compute in add_list l2 (1::nil).
(** Polymorphism *)

Fixpoint generic_append (A:Type) (l1 l2: list A) : list A := 
  match l1 with 
    | nil => l2
    | h::t => h::(generic_append A t l2)
  end.
(** Unlike Ocaml, we make type parameters explicit in Coq.  Here, 
   we've defined a generic append function, which abstracts over
   a type [A].  Notice that the types of the arguments [l1] and
   [l2] depend upon [A], as does the result type.  Notice also
  that when we call this function, we must provide an actual
  type for the instantiation of [A].
*)

Eval compute in generic_append bool l3 l3.
Eval compute in generic_append nat l1 l2.
Eval compute in generic_append _ l3 l3.
Eval compute in generic_append _ nil nil.
(** Coq can usually figure out what the types are, and we can
   leave out the type by just putting an underscore there 
   instead.  But there are cases where it can't figure it
   out (e.g., generic_append _ nil nil).
*)

Fixpoint generic_append' {A:Type} (l1 l2:list A) : list A := 
  match l1 with 
    | nil => l2
    | h::t => h::(generic_append' t l2)
  end.
(** The curly braces tell Coq to make an argument implicit.  That
   means it's up to Coq to fill in the argument for you.  Notice
   that in the recursive call, we didn't have to specify the type. *)

Eval compute in generic_append' l1 l1.
Eval compute in generic_append' l2 l2.
Eval compute in generic_append' nil nil.
Eval compute in generic_append _ nil nil.

(** This won't work though:
Definition foo := generic_append' nil nil.
   We can fix it by either giving enough information in the context
   or by using "@" to override the implicit arguments:
*)
Definition foo : list nat := generic_append' nil nil.
Definition foo1 := @generic_append' nat nil nil.


(** Assignment *)
(** Problem0 *)
Fixpoint length {A:Type} (l:list A): nat :=
  match l with 
    | nil => 0
    | h::t => 1+ (length t)
  end.

Eval compute in length (3::2::1::nil).
Eval compute in length (generic_append' l2 l2).

(** Problem1  Write a function rev that reverses a list.
 rev : forall {A:Type}, list A -> list A *)

Fixpoint rev {A:Type} (l : list A) : list A :=
  match l with 
    | nil => nil
    | h ::t => generic_append' (rev t) (h::nil)
   end.

SearchAbout (list _ ->list _ ->list _).
Locate app.

Eval compute in rev l2.
Eval compute in rev (generic_append' l2 l2).
Eval compute in rev (5::4::3::2::1::nil).

(** Problem 2: Write a function ith that returns the ith element of a list,
 if the list has enough elements, and otherwise returns None.
 We are working zero-based, so for instance, ith 2 (1::2::3::4::nil)
 should return Some 3, whereas ith 4 (1::2::3::4::nil) 
 should return None.*)

Fixpoint ith {A:Type} (n:nat) (l:list A): option A :=
  match l, n with 
    |nil, _ => None
    |h ::t, 0 => Some h
    |h::t, S n' => ith n' t
  end.

Eval compute in ith 2 nil.
Eval compute in ith 4 (1::2::3::4::nil).
Eval compute in ith 0 (1::2::3::4::nil).
Eval compute in ith 2 (1::2::3::4::nil).

(** Problem 3:  Write a generic function comp to compose two functions.
 comp : forall {A B C:Type}, (A -> B) -> (B -> C) -> (A -> C)*)

Definition comp {A B C:Type} (f1: A->B) (f2: B->C) : A-> C :=
  fun (a: A) => f2 (f1 a).

Check comp.

Eval compute in comp length add5.
Eval compute in comp length add5 (3::2::1::nil).
Eval compute in comp length add5 (3::2::1::nil) 10.

(** Problem4:  Write a function sum that adds up all of the nats 
in a list. sum : list nat -> nat  
*)

Fixpoint sum (l:list nat): nat :=
  match l with 
    | nil => 0
    | h ::t => h + (sum t)
end .

Eval compute in sum l1.
Eval compute in sum l2.

(** Problem5: Write a function map that maps a function
 over the elements in a list, producing a new list.
 map : forall {A B:Type}, (A -> B) -> list A -> list B
*)

Fixpoint map {A B:Type} (f : A-> B) (l:list A): list B :=
  match l with 
    | nil => nil
    | h::t => f (h) :: (map f t)
end.

Eval compute in map is_zero (0::1::2::3::0::0::nil).

(** Problem6: Write a generic "fold-right" for a list such that,
 for instance. fold (fun x y => x + y) 0 (1::2::3::nil) evaluates to 6.
 fold : forall {A B:Type}, (A -> B -> B) -> B -> list A -> B 
*)

Fixpoint fold {A B:Type} (f: A -> B -> B) (b: B) (l : list A) : B :=
  match l with 
    | nil => b 
    | h::t => fold f (f h b) t
  end.

Eval compute in fold (fun x y => x + y) 0 (1::2::3::nil).
Eval compute in fold (fun x y => x + y) 10 (1::2::3::nil).

(** Problem7:  Write a function add_pairs that takes a list of pairs of 
 nats and returns the list of the corresponding sums.
 For instance, add_pairs ((1,2)::(3,4)::nil) should 
 return 3::7::nil. add_pairs : list (nat * nat) -> list nat
*)

Fixpoint add_pairs (l : list (nat * nat)): list nat :=
  match l with 
    | nil => nil
    | (a,b)::t => (a+b)::(add_pairs t)
  end.

Eval compute in add_pairs ((1,2)::(3,4)::nil).

(** Problem8: Given the following definition for trees:
Inductive tree (A:Type) : Type := 
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.

Implicit Arguments Leaf [A]. Implicit Arguments Node [A].
*)

Inductive tree (A:Type) : Type := 
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.

Print tree.

(** Write a function which flattens the tree into a list. 
For instance, flatten on the tree:
3 / \ 1 7 / \ / \ o o o o
should yield 1::3::7::nil. flatten : forall {A:Type}, tree A -> list A
*)

(** Problem 10. 
Inductive order : Type := 
| Less 
| Equal
| Greater.

10. Write a function which when given two numbers n and m, 
returns Less if n < m, Equal if n = m, and otherwise returns Greater.
 nat_cmp : nat -> nat -> order

*)

Inductive order : Type := 
| Less 
| Equal
| Greater.

Fixpoint nat_cmp (n m: nat) : order :=
  match n, m with 
    | 0, 0 => Equal
    | 0, S m' => Less
    | S n', 0 => Greater
    | S n', S m' => nat_cmp n' m'
end.

Eval compute in nat_cmp 0 0.
Eval compute in nat_cmp 4 0.
Eval compute in nat_cmp 5 9.


