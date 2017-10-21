Require Import NPeano Arith Bool String List CpdtTactics.
Set Implicit Arguments.

(** A class definition defines an interface for some type.  In this
   case, we say that types A that implement the Show interface have
   a method named show that will convert them to a string. 

   So we can use the generic method "show" on any type A that is
   an instance of the Show class. 

   In general, you can have multiple things in the interface that
   depend upon the type A.
*)
Class Show(A:Type) := {
  show : A -> string
}.

(** Here we define booleans as an instance of the Show class and
   give a definition of the method.  *)
Instance boolShow : Show bool := {
  show := fun (b:bool) => (if b then "true" else "false") % string
}.

Compute show true.
Compute show false.
Eval compute in show 3.

(** This doesn't work because we haven't said how to show a nat.
 We get an even scarier message, 
"[Error: vm_compute does not support existential variables.]"
if we do [Compute show 3], because of that variable [?Show]. *)

(** Now let's define nat as an instance of Show.  We first need
   some helper functions to convert nats to strings. *)

Definition digit2string(d:nat) : string := 
  match d with 
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
    | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
    | 8 => "8" | _ => "9"
  end %string.

(** Alas, it can be difficult to convince Coq that
   this terminates.  So we give it fuel.  But, we
   know how much fuel we should use in this case... *)
Fixpoint digits'(fuel n:nat) (accum : string) : string := 
  match fuel with 
    | 0 => accum
    | S fuel' => 
      match n with 
        | 0 => accum
        | _ => let d := digit2string(n mod 10) in 
               digits' fuel' (n / 10) (d ++ accum)
      end
  end.

(** It's sufficient to use n as the fuel here since
   we know we won't need to divide n by 10 more than
   n times.  We could of course use log_10 n, but there's
   no need to bother here. *)
Definition digits (n:nat) : string := 
  match digits' n n "" with 
    | "" => "0"
    | ds => ds
  end %string.

Require Import Recdef Nat Lia.
Function digits''(n:nat) (accum:string) 
            {measure (fun x:nat => x) n}: string :=
  match n with
  | 0 => accum
  | _ => let d := digit2string(n mod 10) in
         digits'' (n / 10) (d ++ accum)
  end.
Proof.
  intros. apply Nat.div_lt ; lia.
Defined.

(* Now we can define our nat instance for the Show class. *)
Instance natShow : Show nat := { 
  show := digits
}.

Compute show 42.
Compute show (10+2).

(* Importantly, we still have the ability to show booleans. *)
Compute show true.


(** We can also parameterized instances, allowing us to show
    data structures.

    The following is a generic instance in that if we can have two types
    A and B that are instances of the Show class, then we can
    build a generic Show for the product type (A*B).
*)
Instance pairShow(A B:Type)(showA : Show A)(showB : Show B) : Show (A*B) := {
  show := (fun p => "(" ++ (show (fst p)) ++ "," ++ (show (snd p)) ++ ")")
            %string
}.

Compute show (3,4).
Compute show (true,42).

Print pairShow.

(** Similarly, we can define a generic show for lists, as long
   as the elements of the lists are show'able. *)
Definition show_list{A:Type}{showA:Show A}(xs:list A) : string := 
  ("[" ++ ((fix loop (xs:list A) : string := 
             match xs with 
               | nil => "]"
               | h::nil => show h ++ "]"
               | h::t => show h ++ "," ++ loop t
             end) xs))%string.

Instance listShow(A:Type)(showA:Show A) : Show (list A) := {
  show := @show_list A showA
}.

Compute show (1::2::3::nil).
Compute show (true::false::nil).
Compute show ((1,true)::(42,false)::nil).
Compute show ((1::2::3::nil)::(4::5::nil)::(6::nil)::nil).


(** Here is another way to have an anonymous argument,
    other than using the name [_]. *)
Definition showOne {A:Type} `{Show A} (a:A) : string :=
  "The value is " ++ show a.

Compute showOne true.
Compute showOne 7.

Definition showTwo {A B:Type} {sa:Show A} `{Show B} (a:A) (b:B) : string :=
  "First is " ++ show a ++ " and second is " ++ show b.

Compute (showTwo true 7).

(** Type classes are a powerful abstraction tool that fit very well
    with some proof developments.

    One tip is to make type classes as small and simple
    as possible. For example, you probably want to separate out
    the operations you want to use from the properties that
    the implementation is expected to satisfy.
*)


(***********************************************************)

(** Monads are very useful for modeling things that are not just
   pure functions, that have some kind of external effect on the
   world such as reading input or producing output. They're
   essential for modeling statefulness a in pure, stateless,
   functional language like Coq.

   Now we define a generic class for Monads.  Here, it's not a type
   that's a monad, but rather a type constructor (i.e., a function
   from types to types, aka a functor.  Monads have two operations:
   ret and bind.  

   If we think of monads as a pattern for encoding effects, such
   as exceptions or state or non-determinism, then we can think 
   of "M A" as describing side-effecting computations that produce
   a value of type A.  

   The "ret" operation takes a pure (effect-free) value of type A
   and injects it into the space of side-effecting computations.

   The "bind" operation sequences two side-effecting computations,
   allowing the latter to depend upon the value of the first one.
*)

Record Point (T:Type) : Type := {xCord:T; yCord:T}.

Inductive Point' (T:Type) : Type :=
| Build_Point':  T -> T -> Point' T
.

Check {| xCord := 2; yCord :=3 |}.

Check (@Build_Point _ 2 3).

Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

(* As usual, we will use the more convenient notation for bind. *)
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

Inductive IO :Type -> Prop := 
| reti : forall A, A-> IO A
| bindi : forall A B, IO A -> (A -> IO B) -> IO B
| printString : string -> IO bool
| readLine : IO string.


(** One instance of the generic Monad class is the option monad
   defined as follows. It's a bit like exceptions where there
   is only one possible exception: None.
 *)
Instance OptionMonad : Monad option := 
{
  ret := fun {A:Type} (x:A) => Some x ; 
  bind := fun {A B:Type} (x:option A) (f:A -> option B) =>
            match x with 
              | None => None
              | Some y => f y
            end
}.

(** How might we use this monad? We can 'fix' subtraction,
    which ordinarily has odd semantics in Coq, so that any
    computation of a negative number fails and that failure
    propagates to the final result.
*)

Fixpoint subtract (x y:nat) : option nat := 
  match x, y with 
    | x, 0 => ret x
    | 0, S _ => None
    | S x', S y' => subtract x' y'
  end.

Inductive exp := 
| Num : nat -> exp
| Plus : exp -> exp -> exp
| Minus : exp -> exp -> exp.

Instance expShow : Show exp := {
  show := fix show_exp (e:exp) : string := 
              match e with 
                | Num n => show n
                | Plus e1 e2 => 
                  "(" ++ (show_exp e1) ++ "+" ++ (show_exp e2) ++ ")"
                | Minus e1 e2 => 
                  "(" ++ (show_exp e1) ++ "-" ++ (show_exp e2) ++ ")"
              end %string
}.

(** Now we can write an expression evaluator very conveniently: *)
Fixpoint eval (e:exp) : option nat := 
  match e with 
    | Num n => ret n
    | Plus e1 e2 => n1 <- eval e1 ;; 
                    n2 <- eval e2 ;;
                    ret (n1 + n2)
    | Minus e1 e2 => n1 <- eval e1 ;; 
                     n2 <- eval e2 ;;
                     subtract n1 n2
  end.

Goal eval = fun x => None.
unfold eval.
simpl.
Abort.

Example e1 : exp := Plus(Num 2) (Minus(Num 0) (Num 1)).
Compute (eval e1).
(** That's better than normal evaluation: *)
Compute 2 + (0 - 1).

Print "+".

Require Import String.
Inductive Exn(A:Type) : Type := 
| Result : A -> Exn A
| Fail : string -> Exn A.
Arguments Result {A}.
Arguments Fail {A}.

Instance ExnMonad : Monad Exn := 
{
  ret := fun {A:Type} (x:A) => Result x ; 
  bind := fun {A B:Type} (x:Exn A) (f:A -> Exn B) =>
            match x with 
              | Result y => f y
              | Fail s => Fail s
            end
}. 

Fixpoint eval' (e:exp) : Exn nat := 
  match e with 
    | Num n => ret n
    | Plus e1 e2 => n1 <- eval' e1 ;;
                    n2 <- eval' e2 ;;
                    ret (n1 + n2)
    | Minus e1 e2 => n1 <- eval' e1 ;; 
                     n2 <- eval' e2 ;;
                     match subtract n1 n2 with 
                       | None => Fail "underflow"
                       | Some v => ret v
                     end
  end.

Definition tryCatch {A} (e:Exn A) (s:string) (handler:Exn A) : Exn A := 
  match e with 
    | Fail s' => if string_dec s s' then handler else e
    | _ => e
  end.

Definition eval_to_zero (e:exp) := 
  tryCatch (eval' e) "underflow" (ret 0).

Check eval_to_zero.
Compute eval' (Minus (Num 2) (Num 5)).
Compute eval_to_zero (Minus (Num 2) (Num 5)).


(** We can also use monads to model state. *)

Require Import List.
Definition var := string.

(** We define expressions equipped with an imperative
    update: *)
Inductive exp_s : Type := 
| Var_s : var -> exp_s
| Plus_s : exp_s -> exp_s -> exp_s
| Times_s : exp_s -> exp_s -> exp_s
| Set_s : var -> exp_s -> exp_s
| Seq_s : exp_s -> exp_s -> exp_s
| If0_s : exp_s -> exp_s -> exp_s -> exp_s.

Definition state := var -> nat.
Definition upd(x:var)(n:nat)(s:state) : state := 
  fun v => if string_dec x v then n else s x.

(** An evaluator can be written that passes the state
    through everywhere, but it's tedious and error-prone: *)
Fixpoint eval_s (e:exp_s)(s:state) : (state * nat) := 
  match e with 
    | Var_s x => (s, s x)
    | Plus_s e1 e2 => 
      let (s1, n1) := eval_s e1 s in
      let (s2, n2) := eval_s e2 s1 in 
      (s2, n1+n2)
    | Times_s e1 e2 =>
      let (s1, n1) := eval_s e1 s in
      let (s2, n2) := eval_s e2 s1 in 
      (s2, n1*n2)
    | Set_s x e => 
      let (s1, n1) := eval_s e s in 
      (upd x n1 s1, n1)
    | Seq_s e1 e2 => 
      let (s1, n1) := eval_s e1 s in
      eval_s e2 s1
    | If0_s e1 e2 e3 => 
      let (s1, n1) := eval_s e1 s in 
      match n1 with 
        | 0 => eval_s e2 s1
        | _ => eval_s e3 s1
      end
  end.

Definition state_comp(A:Type) : Type := state -> (state*A).

Instance StateMonad : Monad state_comp := {
  ret := fun {A:Type} (x:A) => (fun (s:state) => (s,x)) ; 
  bind := fun {A B:Type} (c : state_comp A) (f: A -> state_comp B) => 
            fun (s:state) => 
              let (s',v) := c s in 
              f v s'
}.

Definition read (x:var) : state_comp nat := 
  fun s => (s, s x).

Definition write (x:var) (n:nat) : state_comp nat := 
  fun s => (upd x n s, n).


(** The evaluator looks much cleaner with the state monad,
    using the functions [read] and [write] to capture interaction
    with the state.
 *)
Fixpoint eval_sm (e:exp_s) : state_comp nat := 
  match e with 
    | Var_s x => read x
    | Plus_s e1 e2 => 
      n1 <- eval_sm e1 ;;
      n2 <- eval_sm e2 ;;
      ret (n1 + n2)
    | Times_s e1 e2 =>
      n1 <- eval_sm e1 ;;
      n2 <- eval_sm e2 ;;
      ret (n1 * n2)
    | Set_s x e => 
      n <- eval_sm e ;;
      write x n 
    | Seq_s e1 e2 => 
      _ <- eval_sm e1 ;; 
      eval_sm e2
    | If0_s e1 e2 e3 => 
      n <- eval_sm e1 ;;
      match n with 
        | 0 => eval_sm e2
        | _ => eval_sm e3 
      end
  end.

(** We can also use monads to model nondeterministic
    evaluation. *)

Inductive exp_nd : Type := 
| Choose_nd : list nat -> exp_nd
| Plus_nd : exp_nd -> exp_nd -> exp_nd
| Times_nd : exp_nd -> exp_nd -> exp_nd.

Definition flatten {A:Type} (xs:list (list A)) := 
  fold_right (fun x a => x ++ a) nil xs.

Instance listMonad : Monad list := {
  ret := fun {A:Type} (x:A) => (x::nil) ;
  bind := fun {A B:Type} (c:list A) (f: A -> list B) => 
            flatten (map f c)
}.

Fixpoint eval_nd (e:exp_nd) : list nat := 
  match e with 
    | Choose_nd ns => ns
    | Plus_nd e1 e2 => 
      n1 <- eval_nd e1 ;;
      n2 <- eval_nd e2 ;;
      ret (n1 + n2)
    | Times_nd e1 e2 => 
      n1 <- eval_nd e1 ;;
      n2 <- eval_nd e2 ;;
      ret (n1 * n2)
  end.
Import ListNotations.

Goal eval_nd = fun _ => nil.
unfold eval_nd. simpl.
Abort.

Compute eval_nd (Plus_nd (Choose_nd (1::2::nil)) (Choose_nd (3::4::nil))).

(** Monads ideally satisfy the following laws, and a good exercise
    is to try to show that any monad you define satisfies these laws. *)

Class Monad_with_Laws (M: Type -> Type){MonadM : Monad M} :=
{
  m_left_id : forall {A B:Type} (x:A) (f:A -> M B), bind (ret x) f = f x ;
  m_right_id : forall {A B:Type} (c:M A), bind c ret = c ;
  m_assoc : forall {A B C} (c:M A) (f:A->M B) (g:B -> M C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g)
}.

(** This demonstration is easy for the option monad: *)

Instance OptionMonadLaws : @Monad_with_Laws option _ := {}.
  auto.
  intros ; destruct c ; auto.
  intros ; destruct c ; auto.
Defined.

(** In fact, not all monads we want to define will satisfy
    these laws. In particular, the requirement of equality above
    causes trouble when the monad contains functions, as in the
    case of the state monad. We can get around that difficulty
    by parameterizing the monad laws with an equivalence relation
    that captures the notion of equality we want to use.
*)
