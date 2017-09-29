(** Let's build a provably correct (but very simple) compiler! We'll see
    that with the right tactic automation, the proof can be extremely simple. 
   This example is taken from the [Library StackMachine] chapter of CPDT.

#<small>#
   You'll need the tarball of open-source libraries from CPDT, which can be
   obtained from Adam Chlipala's website:
#<a href="http://adam.chlipala.net/cpdt/cpdtlib.tgz">#
      [http://adam.chlipala.net/cpdt/cpdtlib.tgz]
#</a>#

   You will need to compile the source, which can be done as follows in
   the cpdtlib:
#<pre>#
      coqc -R . Cpdt *.v
#</pre>#

   To make the compiled CPDT libraries automatically available from
   within Emacs, put this text into .dir-locals.el:
#<pre>#
      ((coq-mode . ((coq-prog-args . ("-emacs-U" "-I" "../cpdtlib")))))
#</pre>#

   From coqide, you can use the -R command:
#<pre>#
      coqc -R <cpdtlib> Cpdt lecture4.v
#</pre>#

   where [<cpdtlib>] is the full pathname of the cpdtlib directory.
#</small>#
*)


Require Import Bool Arith List CpdtTactics.
Require Import Unicode.Utf8.

(** This command tells Coq to automatically make some arguments implicit when
   you write definitions.  In general, it will make implicit something that
   it can easily figure out from the other arguments (e.g., types often)
   and saves you from using curly braces and so forth.  Figuring out what
   it decides to make implicit isn't always easy.  When you Print a definition,
   it tells you what arguments are implicit, so that helps.  You get used
   to what it decides pretty quickly... *)
Set Implicit Arguments.

(** Let's start by defining some syntax for a simple
    language of arithmetic expressions. This is just
    an abstract syntax tree -- not a computation but
    a data structure representing one.
  *)
Inductive binop : Type := Plus | Times.
Check binop.
Check Plus.
Inductive ternop: Type := If.

Inductive exp : Type := 
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp
| Ternop: ternop -> exp -> exp -> exp -> exp.

(** Using Coq, we can describe the _meaning_ of the computation
    denoted by an abstract syntax tree. We can think of this
    as giving a mathematical description of the computation
    (or as a compilation directly into Coq).
*)
Definition binopDenote (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
  end.

Print eq.
Print le.

Definition ternopDenote (b:ternop) : nat -> nat -> nat -> nat := 
  match b with 
    | If => fun (e1 e2 e3 : nat) => match e1 with 
                      | 0 => e2
                      | S n => e3
                    end
  end.

Eval compute in ternopDenote If 3 4 5.

Fixpoint expDenote (e:exp) : nat := 
  match e with 
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
    | Ternop b e1 e2 e3 => (ternopDenote b) (expDenote e1) (expDenote e2)(expDenote e3)
  end.

(** Now let's define a stack-machine target language for a
    compiler. A program is a list of instructions that
    manipulate a stack of operands.
  *)

Inductive instr : Type := 
| iConst : nat -> instr
| iBinop : binop -> instr
| iTernop: ternop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(** We can also give a denotation for stack machine programs,
    in terms of the output stack. However, not all stack machine programs make sense, since
    there might not be enough arguments on the stack for a
    binary operator. We give these programs the denotation None.
  *)

Definition instrDenote (i:instr) (s:stack) : option stack := 
  match i with 
    | iConst n => Some (n::s)
    | iBinop b => 
      match s with 
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2::s')
        | _ => None
      end
    | iTernop b =>
      match s with 
        | arg1 :: arg2 :: arg3 :: s' => Some ((ternopDenote b) arg1 arg2 arg3 :: s')
        | _ => None
end
  end.

Fixpoint progDenote (p:prog) (s:stack) : option stack := 
  match p with 
    | nil => Some s
    | i::p' => 
      match instrDenote i s with 
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

Eval compute in progDenote (iConst 3::iConst 4::iBinop Times::nil) nil.
Import ListNotations.
Eval compute in progDenote [iConst 3; iConst 4; iBinop Times] [].
Eval compute in progDenote [iConst 3; iConst 4; iConst 5; iTernop If] [].

(** Now let's write a compiler from the source language
    to the argument language! *)

Fixpoint compile (e:exp) : prog := 
  match e with 
    | Const n => [iConst n]
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
    | Ternop b e1 e2 e3 => compile e3 ++ compile e2 ++ compile e1 ++ iTernop b :: nil
  end.

(** Wouldn't it be great if our compiler were correct? We can
    prove that by relating the denotations of the source program
    and its compilation. *)

Lemma compile_correct'' : forall e p s, 
    progDenote (compile e ++ p) s = progDenote p (expDenote e::s).
  Proof.
    induction e.
    - simpl. reflexivity.
    - simpl. intros. repeat rewrite <- app_assoc. rewrite IHe2. rewrite IHe1. simpl. reflexivity.
    - simpl. intros. repeat rewrite <- app_assoc. rewrite IHe3. rewrite IHe2. rewrite IHe1. simpl. reflexivity.
  Qed.

Lemma compile_correct' : forall e p s, 
    progDenote (compile e ++ p) s = progDenote p (expDenote e::s).
  Proof. 
    (** [crush] is a magic tactic provided by [CPDT] that manages to knock off
       a lot of obligations for us.  Later, we will look at how [crush] is
       defined to build our own proof-automation.  But in some sense, this is
       the ideal proof in a readability-sense.  It's the equivalent of writing
       "by induction on e".  *)
    induction e ; crush.
    Qed.

Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.  

  (** And now we can use this lemma to prove our desired theorem. *)  
  intros.
  rewrite (app_nil_end (compile e)).
  rewrite compile_correct'.  
  reflexivity.
Qed.

(***** Second example ******)

Inductive type : Set := Nat | Bool.


(** Notice that both [tbinop] and [texp] are *indexed* by [type]s.  That is
   to say, we are reflecting some structure in the types of the constructors.

   For example, in the case of [TBinop], we are requiring that we pass in
   a [binop] indexed by [t1], [t2], and [t], and that the sub-expressions
   were built from constructors that are indexed by [t1] and [t2] respectively,
   and we get out a [texp] indexed by [t].  

   GHC and OCaml provide support for this kind of indexed data type now,
   though it's called "generalized abstract data types" (GADTs) in those
   contexts.  Coq (and type theory) have had them for a long time...
*)
Inductive tbinop : type -> type -> type -> Type :=
| TPlus  : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq    : forall t, tbinop t t Bool
| TLt    : tbinop Nat Nat Bool.

Inductive texp : type -> Type :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall (t1 t2 t:type), tbinop t1 t2 t -> texp t1 -> 
                                  texp t2 -> texp t.

(** This is a kind of a funny function -- it's mapping our names for
   types, [Nat] and [Bool], to actual Coq types.  This is not something
   you can write in Ocaml or Coq.
*)
Definition typeDenote (t : type) : Type :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(** Look carefully at the type of [tbinopDenote] and see how this
   matches up with the definition. *)
Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => eqb
    | TLt => leb
  end.

Check tbinopDenote.
Check TBinop.

(** Similarly, here we can see that [texpDenote] takes an [texp] indexed
   by a [type] named [t], and returns a value of the Coq type [typeDenote t].
   It's the ability to (a) use dependent types, (b) write functions from
   values to types, (c) index data constructor types with other data that
   really provides the power to capture this here.  

   In essence, we are proving that our compiler preserves types appropriately
   when we use this kind of indexing.  And it's all happening more or less
   for free.
*)
Fixpoint texpDenote (t:type) (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Definition tstack := list type.

(** A tinstr describes how one stack (at the type level) is mapped
    to another stack by a single instruction. *)
Inductive tinstr : tstack -> tstack -> Type :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiBinop : forall arg1 arg2 res s,
  tbinop arg1 arg2 res
  -> tinstr (arg1 :: arg2 :: s) (res :: s).

(** The action of an entire program is a tprog. *)
Inductive tprog : tstack -> tstack -> Type :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

(** vstack maps a tstack into a tuple containing the
    denotations of all the types in the stack *)
Fixpoint vstack (ts : tstack) : Type :=
  match ts with
    | nil => unit
    | t :: ts' => (typeDenote t) * (vstack ts')
  end%type.

(** We can lift the action of an instruction to
    a mapping over real types.
 *)
Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop  _ b => fun s =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.

(** Then, concatenating with a program or instruction is just composition of the denotations. *)
Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Require Import Coq.Logic.FunctionalExtensionality.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TBinop b e1 e2 => (tconcat (tcompile e2 _)
                        (tconcat (tcompile e1 _)
                                 (TCons (TiBinop _ b) (TNil _))))
  end.

Lemma tconcat_correct : forall ts ts' ts''
  (p : tprog ts ts') (p' : tprog ts' ts'') (s : vstack ts),
  tprogDenote (tconcat p p') s = tprogDenote p' ( tprogDenote p s).
Proof.
  induction p; crush.
Qed.

(** A [Hint] is a way of registering a definition, such as [tconcat_correct],
   as something we want to use within certain tactics, such as [crush] or
   [auto].  Effectively, by registering [tconcat_correct] as a [Hint Rewrite],
   we are telling [crush] (and [auto]) that it should try to rewrite the
   goal using this lemma as part of the search for a proof.  

   Adding hints is a great way to get more powerful tactics.  But it does
   have a downside in that it can blow up the time it takes for a tactic to
   find a proof.  So we will see some techniques for using hints in a more
   modular fashion.  
*)
Hint Rewrite tconcat_correct.

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
Proof.
  induction e; crush.
Qed.
Hint Rewrite tcompile_correct'.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.

Print tcompile_correct'.
(** [Extraction] and [Recursive Extraction] allow us to extract OCaml
   code from a Coq development.  We can also extract Haskell or Scheme.
   Look carefully at the extracted code and compare with the Coq
   definitions. *)
Recursive Extraction tcompile.

