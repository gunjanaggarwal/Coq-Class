(** The top-level command [Check <exp>] tells you the type of the given exp. *)
Check True.
Check False.

(** [True] and [False] are propositions or something classified by the type [Prop].  
   They are not to be confused with [true] and [false] which are booleans.
   The distinction is roughly, that [true] and [false] are objects, whereas
   [True] and [False] are types.  What are the elements of the type [True]?
   They are all the *proofs* that allow us to conclude "True".  In contrast,
   the object [true] doesn't really name a collection of things.  

   So what are some of the elements or proof objects in the special 
   type [True]?
*)
Print True.
(** Aha!  We see that one element is the constructor [I].  It's a way 
   (in fact, the best way) to build a proof whose conclusion is the
   trivial theorem [True].  
*)
Check I.
(** But [I] is not the only way to build an object of type [True].  Another
   example is:
*)
Check (fun x => x) I.
(** And we will see many more examples of ways to construct a proof of [True].
   However, it will turn out that if a (closed) expression e : True, then

   So in general, an element of [Prop], such as [True], is the 
   name of a theorem, and at the same type, names a collection of terms that
   correspond to proofs of that theorem. 

   What about [False]?
*)
Print False.
(** [False] is a funny inductive definition which has no
   constructors.  So, there's no easy way to build an object that
   has type [False].  A very, very deep result about Coq is that in
   fact, there is no closed term E such that E : False.  In other
   words, there's no way construct a proof of False, and that's a
   very good thing.

   Now remember last time, that I said that all functions in Coq
   must terminate?  Well, one reason why is that if we had diverging
   computations, a la OCaml, then we would have a way to build
   a term E of type False.  For instance, in OCaml, we can define:

   letrec loop () : t = loop ()

   for any type [t] that we like, includng an empty type.  This
   means that in OCaml, every type has an element and thus we
   can't use OCaml types to represents propositions such as [False].
   Another way to say this is that in OCaml, the "logic" of the 
   language is "inconsistent." 

   There are other good reasons why Coq functions are required
   to terminate.  One is that the type-checker must sometimes
   normalize (i.e., simplify) expressions to see if they are equal.  
   If that normalization process could diverge, then so could
   type-checking.

   Later on, we'll see how it's possible to *model* computations
   that might diverge.
*)


(** The top-level command [Locate "..."] helps to locate a symbol that's defined
   with notation.  In this case, we are searching for the notation for logical
   "and". *)
Locate "_ /\ _".
Check and.

(** The top-level command [Print <id>] prints the definition of a 
   given identifier.  Note that [and] is just an inductive definition
   with one constructor, [conj] which takes two [Prop]s as arguments,
   and produces a [Prop] as a result. *)
Print and.
Locate "_ * _".
Check prod.
Print prod.
Locate "_ \/ _".
Check or.

(** Logical [or] is also just an inductive definition, but this
   time it has two constructors, one for the left and one for 
   the right. *)
Print or.

(** I'm going to start a new module named [M1] so that I don't
   pollute the top-level namespace.  We end the module by writing
   [end M1.] -- see below. *)
Module M1.

  (** Now we can start building some interesting proofs. *)
  Definition proof_of_true_and_true : True /\ True := 
    conj I I.

  Definition proof_of_true_or_false : True \/ False := 
    or_introl I.

  Definition proof_of_false_or_true : False \/ True := 
    or_intror I.
  
  (** What about implication?  This can be represented as a
     function.  That is, we can think of "A implies B" as 
     a function which takes evidence of A and constructs
     evidence of B from it.  In fact, we will use the notation
     "->" to denote both functions and implication.  And we
     will use [fun x => ...] to build a function, or evidence
ccer     of an implication.  For instance: *)
  Definition t0 {A:Prop} : A -> True := 
    fun (H:A) => I.

  Definition t1 {A B:Prop} : A -> B -> A /\ B := 
    fun (HA:A) (HB:B) => conj HA HB.
  
  (** This example shows taking apart some evidence.  In this
     case, we are given evidence of [A /\ B] and we need to
     construct from it evidence of [A].  So we use a pattern
     match to tear apart the proof of [A /\ B], since we know
     that it must've been built from [conj HA HB] where [HA]
     is a proof of [A] and [HB] is a proof of [B].  *)
  Definition t2 {A B:Prop} : A /\ B -> A := 
    fun (H : A /\ B) => 
      match H with 
        | conj H1 H2 => H1
      end.
  
  Definition t3 {A B:Prop} : A /\ B -> B :=
    fun (H: A /\ B) => 
      match H with
        | conj H1 H2 => H2
      end.
    
  Definition t4 {A B C:Prop} : 
    (A -> C) /\ (B -> C) -> (A \/ B) -> C := 
    fun (H1:(A->C)/\(B->C)) (H2:A\/B) => 
      match H1 with 
        | conj H3 H4 => match H2 with 
                          | or_introl H5 => H3 H5
                          | or_intror H6 => H4 H6
                        end
      end.

  Definition t5 {A:Prop} : False -> A := 
    fun (H:False) => 
      match H with 
      end.

  Definition t6 {A B C D:Prop} (H1:A -> B \/ C) : 
    (B -> D) -> (C -> D) -> (A -> D) := 
    fun H2 H3 H4 => 
      let H5 := H1 H4 in 
      t4 (conj H2 H3) H5.

  Locate "~ _".
  Check not.
  Print not.

  (** Negation [~A] is just an abbreviation for [A -> False]. *)
  Definition t7 {A B C : Prop} : 
    ~ (A /\ B) -> A -> B -> C := 
    fun (H1 : (A/\B) -> False) (H2:A) (H3:B) => 
      match H1 (conj H2 H3) with
      end.

  Definition t7' : forall {A B C:Prop}, 
    ~ (A /\ B) -> A -> B -> C.                   
    Abort.

  Definition t7'' : 
    forall {A B C : Prop} (H1:~ (A /\ B)) (H2 : A) (H3 : B), C.
    Abort.

  Inductive animal : Type := 
  | Cow | Duck | Pig | Platypus.
    
  (** In addition to the built-in [Prop]s, we can define new 
     propositional constructions.  For example, below I define
     a proposition called [has_bill] which is a predicate on 
     [animal]s.  
   *)
  Definition has_bill (a:animal) : Prop := 
    match a with 
      | Duck => True
      | Platypus => True
      | _ => False
    end.
  
  (** Here's another predicate on animals... *)
  Definition live_birth (a:animal) : Prop := 
    match a with 
      | Cow => True
      | Pig => True
      | _ => False
    end.
  
  (** Then we can use these definitions to construct a more
     interesting theorem.  Notice that here I'm universally
     quantifying over an animal, using [forall].  *)
  Definition darwin : 
    forall a:animal, has_bill a -> ~ live_birth a := 
    fun (a:animal) => 
      match a return has_bill a -> ~live_birth a
      with 
        | Duck => fun H1 H2 => H2
        | Platypus => fun H1 H2 => H2
        | Cow => fun H1 H2 => H1
        | Pig => fun H1 H2 => H1
      end.

  Definition moos (a:animal) : Prop := 
    match a with 
      | Cow => True
      | _ => False
    end.
  
  Locate "exists".
  Check ex.
  Print ex.

  (** Notice that exists is not primitive and is in fact encoded using forall. Notice that the
      variable mentioned in forall is really a parameter to the [exists_intro] constructor, allowing
      us to construct a proof of an existential claim using _any_ witness. 
      The [A] and [P] parameters to [ex_intro] are implicit. We can force ourselves to
      provide them explicitly by using [@ex_intro] instead. *)

  Definition darwin2 : exists a:animal, (moos a /\ live_birth a) := 
    ex_intro (fun a => moos a /\ live_birth a) Cow (conj I I).

  (** Sometimes, Coq can figure out what a missing argument is and
     we can omit it by putting in an underscore "_" as in the 
     example below. *)
  Definition darwin3 : exists a:animal, (moos a /\ live_birth a) := 
    ex_intro _ Cow (conj I I).

End M1.

Module PSET1_EX1.

(**PROBLEM1:  *)

  Definition X1 {A B C D:Prop} : (B /\ (B -> C /\ D)) -> D :=
  fun (H1: B /\ (B -> C /\ D))  =>
    match H1 with 
      | conj (H2) (H3) => 
        let H4 :(C /\ D ):= (H3 H2) in 
        match H4 with 
          | conj H5 H6 => H6
        end
  end.
Print and.

(**PROBLEM2:  *)
  Definition X2 {A B C:Prop} : ~(A \/ B) -> B -> C :=
  fun (H1: A \/ B -> False) (H2:B) =>
    let H3: (A\/B) := (or_intror H2) in 
    match H1 H3 with 
    end.

(** PROBLEM3: *)
  Definition X3 {A B C:Prop} :  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C) :=
  fun (H1 : A /\ (B \/ C)) =>
    match H1 with 
      | conj H2 H3 => match H3:(B \/ C) with
                      |or_introl b => or_introl (conj H2 b) 
                      |or_intror H5 => or_intror (conj H2 H5)
                      end
    end.

(** PROBLEM 4: To solve the following, you'll need to figure 
out what the definition of "<->" is and how to work with it... *)
Locate "_ <-> _".
Check iff.
Print iff.

Definition X4 {A:Prop} : A <-> A :=
    conj (fun (a:A) => a ) (fun (a:A) => a).

Print and.
(** PROBLEM4: *)
Definition X5 {A B:Prop} : (A <-> B) <-> (B <-> A):=
  conj 
   (fun H1 =>
    match H1 with
      | conj H2 H3 => conj H3 H2
    end) 

   (fun H1 =>
    match H1 with
      | conj H2 H3 => conj H3 H2
    end) 
.

Print iff.
(** PROBLEM 5: *)

Definition assoc {A B  C: Prop} (f1:A -> B) (f2:B -> C) (a:A) : C :=
    f2 (f1 a).

Definition X6 {A B C:Prop} : (A <-> B) -> (B <-> C) -> (A <-> C):=
  fun (H1:((A -> B) /\ (B -> A))) (H2: ((B-> C) /\ (C -> B))) =>
    match H1, H2 with
    | conj h11 h12 , conj h21 h22 => conj (assoc h11 h21) (assoc h22 h12)
    end.

Lemma uncurrying: forall (A B C :Prop),
((A/\B)->C) <-> (A->B->C).
Abort.

(** PROBLEM think-about-it *)
Definition not_pos {A}: A \/ ~A.
Admitted.

(** Definition haltingProblem (n:N) : (n th TM halts) \/ 
(n th TM never halts). *)
 
(** Building proof objects by hand can be extremely difficult.
   So instead, we're going to use some *tactics* to construct
   these objects.  Some useful tactics include the following:

   auto   -- solves trivial goals such as "True" and "3 = 3" or
             "x = x".

   intro  -- given a goal A -> B, introduces A as an assumption,
             leaving B as the result.  It's the same as writing
             [refine (fun H:A => _)].

   intros -- same as above but introduces a bunch of assumptions.
             For instance, if our goal is A -> B -> C -> D, then
             intros will introduce hypotheses H1:A, H2:B, and
             H3:C and leave us with the goal D.  You can also
             give explicit names for the hypotheses as in 
             intros H1 H2 H3.

   split --  if the goal is A /\ B, breaks this into two sub-goals,
             first A and then B.

   destruct -- if we have a hypothesis [H : A /\ B] then we can 
               break it into two hypotheses [H1 : A] and [H2 : B].
               using [destruct].  

   simpl --  simplifies the goal by reducing expressions as much 
             as possible.  For instance, if our goal is
             [1 + 3 = 2 + 3], then calling [simpl] will reduce
             the goal to [4 = 4] which we can solve by auto.

   left --   given the goal A \/ B, reduces the goal to proving
             just A.  

   right --  given goal A \/ B, reduces the goal to proving B.

   apply H -- apply the hypothesis H to solve the current goal.
              This only works when H names a hypothesis that
              matches the given goal.

   See also http://adam.chlipala.net/itp/tactic-reference.html
   for a better list.
*)

(** Re-doing the examples above using tactics. *)
Module M2.

  (** Notice that I didn't use ":=" but terminated the definition
     with a period.  This drops you into tactic mode. *)
  Definition proof_of_true_and_true : True /\ True.
  Proof.  (** not necessary, but a good visual indicator. *)
    (** prove True /\ True *)
    split. (** leaves us with two goals *)
      (** First goal:  True *)
      auto.
      (** Second goal: True *)
      auto.
   Qed.  (** claim that we've solved all goals. *)

  (** We can print out the proof object that the tactics
     constructed for us... *)
  Print proof_of_true_and_true.

  (** Instead of using the keyword [Definition] we can also
     use the keywords [Lemma] and [Theorem].  *)
  Lemma proof_of_true_and_true' : True /\ True.
  Proof.  
    auto.  (** actually, auto will knock this off. *)
  Qed.

  Theorem prof_of_true_and_true'' : True /\ True.
  Proof.
    (** we can use previously existing proofs. *)
    apply proof_of_true_and_true'.
  Qed.

  Definition proof_of_true_or_false : True \/ False.
    Abort.

  Definition proof_of_false_or_true : False \/ True.
    Abort.
    
  Lemma t0 {A:Prop} : A -> True.
  Proof.
    intro.
    auto.
  Qed.    

  Lemma t1 {A B:Prop} : A -> B -> A /\ B.
  Proof.
    auto.
  Qed.

  Lemma t2 {A B:Prop} : A /\ B -> A.
  Proof.
    tauto.
  Qed.

  Lemma t3 {A B:Prop} : A /\ B -> B.
  Proof.
    (** It's generally a bad idea to let Coq pick the names for you. 
       We can usually give names that we want. *)
    intro H.
    destruct H as [H1 H2].
    apply H2.
  Qed.

  Lemma t3' {A B:Prop} : A /\ B -> B.
  Proof.
    (** We can also do some destruction as we introduce things. *)
    intros [H1 H2].
    apply H2.
  Qed.

  Lemma t3'' {A B:Prop} : A /\ B -> B.
  Proof.
    (** There are some fancier decision procedures that can knock this
       sort of thing off, such as [firstorder].  For now, try to avoid
       using these so that you can understand the basic tactics --- you
       will need them. *)
    firstorder.
  Qed.

  Definition t4 {A B C:Prop} : 
    (A -> C) /\ (B -> C) -> (A \/ B) -> C.
  Proof.
    firstorder.
  Qed.

  Definition t5 {A:Prop} : False -> A.
  Proof.
    firstorder.
  Qed.

  Definition t6 {A B C D:Prop} : 
    (A -> B \/ C) -> (B -> D) -> (C -> D) -> (A -> D).
  Proof.
    firstorder.
  Qed.

  Locate "~ _".
  Check not.
  Print not.

  (** Negation [~A] is just an abbreviation for [A -> False]. *)
  Definition t7 {A B C : Prop} : 
    ~ (A /\ B) -> A -> B -> C.
  Proof.
    firstorder.
  Qed.
  
  (** We can write the type of [t7] using [forall], which shows that
      arrow types are really just a special case of a more powerful
      dependent type construct in which the type on the right-hand
      side of the arrow can mention the name of the argument. *)
  Definition t7' : forall {A B C:Prop}, 
    ~ (A /\ B) -> A -> B -> C.                   
  Proof.
    firstorder.
  Qed.

  Definition t7'' : 
    forall {A B C : Prop} (H1:~ (A /\ B)) (H2 : A) (H3 : B), C.
  Proof.
    firstorder.
  Qed.

  Inductive animal : Type := 
  | Cow | Duck | Pig | Platypus.
    
  Definition has_bill (a:animal) : Prop := 
    match a with 
      | Duck => True
      | Platypus => True
      | _ => False
    end.
  
  Definition live_birth (a:animal) : Prop := 
    match a with 
      | Cow => True
      | Pig => True
      | _ => False
    end.
  
  (** Then we can use these definitions to construct a more
     interesting theorem.  Notice that here I'm universally
     quantifying over an animal, using [forall].  *)
  Definition darwin : 
    forall a:animal, has_bill a -> ~ live_birth a.
  Proof.
    intro a.
    (** We need to tear apart [a] -- this is done with destruct,
        just as we tear apart a conjunection [A /\ B].  In 
        general, destruct does our pattern match for us and 
        leaves us with the corresponding goals. *)
    destruct a.
      (** [a = Cow] *)
      (** It's not immediately clear that this is trivial, unless
         we [simpl]ify the goal. *)
      simpl.
      auto.
      (** [a = Duck] *)
      (** auto will do the simplification for you if it needs to. *)
      auto.
      (** [a = Pig] *)
      auto.
      (** [a = Platypus] *)
      auto.
  Qed.

  (** We can string together tactics using a semicolon.  When you
     write [t1 ; t2], then [t1] is run on the current goal G.  This
     produces new sub-goals G1, G2, ..., Gn.  Then [t2] is run on
     each of these sub-goals.  So we can simplify the proof above
     as follows: *)
  Definition darwin' : 
    forall a:animal, has_bill a -> ~ live_birth a.
  Proof.
    destruct a ;   (** automatically introduces a *)
    auto.
  Qed.

  Definition moos (a:animal) : Prop := 
    match a with 
      | Cow => True
      | _ => False
    end.
  
  Locate "exists".
  Check ex.
  Print ex.

  Definition darwin2 : exists a:animal, (moos a /\ live_birth a).
  Proof.
    (** The [exists] tactic is the way to solve an existential goal. 
       You have to give the witness. *)
    exists Cow.
    simpl.
    auto.
  Qed.


End M2.

Module PSET1_EX2.

(** Now remove the tauto tactics and redo these problems using only 
the following tactics:
intros, apply, destruct, unfold, split, contradiction, left, right
(Hopefully we haven't left off any that you may need. 
In general, don't use things like firstorder or tauto that 
automatically solves goals. We want you to perform the basic steps 
to see what is going on.)
*)


Lemma X1 {A B C D:Prop} : 
    (B /\ (B -> C /\ D)) -> D.
  Proof.
    intros H1.
    destruct H1.
    apply H0 in H.
    destruct H.
    apply H1.
  Qed.

Check not.
Print not.
Lemma X2 {A B C:Prop} : 
    ~(A \/ B) -> B -> C.
  Proof.
  intros.
  unfold not in H.
  apply (@or_intror A ) in H0.
  apply H in H0.
  destruct H0.
  Qed.

  Lemma X3 {A B C:Prop} : A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
  Proof.
    intros.
    destruct H.
    destruct H0.
     Show Proof.
   - left.
     Show Proof.
     split.
     Show Proof.
     + apply H.
     + apply H0.
   - right.
     Show Proof.
     split.
     Show Proof.
     apply H.
     apply H0.
  Qed.

Lemma X4 {A:Prop} : A <-> A.
  Proof.
    intros.
    Show Proof.
    split.
    - intros a. apply a.
    - intros a. apply a.
  Qed.

Lemma X5 {A B:Prop} :(A <-> B) <-> (B <-> A).
  Proof.
    intros.
    Show Proof.
    unfold iff.
    split.
    - intros H. destruct H.
      split.
       + apply H0.
       + apply H.
       Show Proof.
    - split.
      destruct H.
      + apply H0.
      + apply H.
  Qed.

Lemma assoc {A B C: Prop}: (A -> B) /\ (B-> C) -> (A -> C).
  Proof.
    intros.
    destruct H.
    apply H1.
    apply H.
    assumption.
  Qed.

Lemma X6 {A B C:Prop} : (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    intros.
    unfold iff.
    unfold iff in H.
    unfold iff in H0.
    destruct H.
    destruct H0.
    split.
    - Show Proof.
      apply @assoc with (B:=B).
      Show Proof.
      split;assumption.
    - apply @assoc with (B:=B).
      split; assumption.
  Qed.



