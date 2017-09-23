Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.

Definition var := string.

Inductive binop := Plus | Times | Minus.

Inductive aexp : Type := 
| Const : nat -> aexp
| Var : var -> aexp
| Binop : aexp -> binop -> aexp -> aexp.

Inductive bexp : Type := 
| Tt : bexp
| Ff : bexp
| Eq : aexp -> aexp -> bexp
| Lt : aexp -> aexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp
| Not : bexp -> bexp.

Inductive com : Type := 
| Skip : com
| Assign : var -> aexp -> com
| Seq : com -> com -> com
| If : bexp -> com -> com -> com
| While : bexp -> com -> com.

Definition state := var -> nat.

Definition get (x:var) (s:state) : nat := s x.

Definition set (x:var) (n:nat) (s:state) : state := 
  fun y => 
    match string_dec x y with 
        | left H => n 
        | right H' => get y s
    end.

Definition eval_binop (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
    | Minus => minus
  end.

Fixpoint eval_aexp (e:aexp) (s:state) : nat := 
  match e with 
    | Const n => n
    | Var x => get x s
    | Binop e1 b e2 => (eval_binop b) (eval_aexp e1 s) (eval_aexp e2 s)
  end.



Fixpoint eval_bexp (b:bexp) (s:state) : bool := 
  match b with 
    | Tt => true
    | Ff => false
    | Eq e1 e2 => Nat.eqb (eval_aexp e1 s) (eval_aexp e2 s)
    | Lt e1 e2 => Nat.ltb (eval_aexp e1 s) (eval_aexp e2 s)
    | And b1 b2 => eval_bexp b1 s && eval_bexp b2 s
    | Or b1 b2 => eval_bexp b1 s || eval_bexp b2 s
    | Not b => negb (eval_bexp b s)
  end.

(** thisis a partial function. data structure*)
Inductive eval_com : com -> state -> state -> Prop := 
| Eval_skip : forall s, eval_com Skip s s
| Eval_assign : forall s x e, eval_com (Assign x e) s (set x (eval_aexp e s) s)
| Eval_seq : forall c1 s0 s1 c2 s2, 
               eval_com c1 s0 s1 -> eval_com c2 s1 s2 -> eval_com (Seq c1 c2) s0 s2
| Eval_if_true : forall b c1 c2 s s',
                   eval_bexp b s = true -> 
                   eval_com c1 s s' -> eval_com (If b c1 c2) s s'
| Eval_if_false : forall b c1 c2 s s',
                   eval_bexp b s = false -> 
                   eval_com c2 s s' -> eval_com (If b c1 c2) s s'
| Eval_while_false : forall b c s, 
                       eval_bexp b s = false -> 
                       eval_com (While b c) s s
| Eval_while_true : forall b c s1 s2 s3, 
                      eval_bexp b s1 = true -> 
                      eval_com c s1 s2 -> 
                      eval_com (While b c) s2 s3 -> 
                      eval_com (While b c) s1 s3.

(** Notation "âŸ¨ A , S âŸ© â‡“ T" := (eval_com A S T) (at level 100). *)

(* y := 1; x := 2; while 0 < x { y := y * 2; x := x - 1 } *)
Definition prog1 := 
  Seq (Assign "y" (Const 1))
  (Seq (Assign "x" (Const 2))
       (While (Lt (Const 0) (Var "x"))
              (Seq (Assign "y" (Binop (Var "y") Times (Const 2)))
                   (Assign "x" (Binop (Var "x") Minus (Const 1)))))).
Ltac myinv H:= inversion H; subst; simpl in *; clear H.

Theorem prog1_prop: forall s1 s2, eval_com prog1 s1 s2 -> get "x" s2 =0.
Proof.
unfold prog1; intros.
Ltac foo :=
match goal with
| [H: eval_com (Seq _ _) _ _ |- _] => myinv H
| [H: eval_com (Assign _ _) _ _ |- _] => myinv H
end.

Ltac bar :=
match goal with
| [H: eval_com (While _ _) _ _ |- _] => myinv H; try discriminate; repeat foo
end.
repeat foo.
bar.
bar. compute in H1. clear H1. myinv H7; simpl in *.
- compute . reflexivity.
- compute in H2. compute in H1. discriminate.
Qed.


Theorem seq_assoc : 
  forall c1 c2 c3 s1 s2, 
    eval_com (Seq (Seq c1 c2) c3) s1 s2 -> 
    eval_com (Seq c1 (Seq c2 c3)) s1 s2.
Proof.
intros. repeat foo. apply Eval_seq with (s1:=s4).
- assumption.
- apply Eval_seq with (s1:=s3) ; assumption.

(**
Abhishek's proof
intros. repeat foo. eauto using Eval_seq.
*)
Qed.



Definition prog2 := While Tt Skip.

Lemma wtce: forall c s1 s2, 
    eval_com c s1 s2 -> c = prog2 -> False.
Proof.
 intros c s1 s2 H. unfold prog2.
 induction H; repeat (intros; try discriminate).
- myinv H0. discriminate.
- myinv H2. apply IHeval_com2. reflexivity.
Qed.

Lemma while_true_cant_eval: forall s1 s2, ~ eval_com prog2 s1 s2.
Proof.
  unfold not, prog2. intros.
  apply (wtce _ s1 s2 H eq_refl).
Qed.


Ltac myinj H := injection H ; intros ; subst ; clear H.

Lemma while_true_imp_false : forall c s1 s2, eval_com c s1 s2 -> 
                               forall b c', (forall s, eval_bexp b s = true) -> 
                                             c = While b c' -> False. 
Proof.
  intros c s1 s2 H. induction H; repeat (intros; try discriminate).
  - intros. myinv H1. congruence.
  - intros. apply IHeval_com2 with (b0:=b0)(c':=c'); assumption.

(** greg's proof
  Ltac foo' := 
  match goal with 
    | [ H : ?x _ _ = ?x _ _ |- _ ] => myinj H
    | [ H : forall s, eval_bexp _ s = _,
        H' : eval_bexp _ ?s0 = _ |- _] => 
      specialize (H s0) ; congruence
    | [ H : forall b c, _ -> _ |- _ ] => eapply H ; eauto
  end.

  induction 1 ; intros ; try discriminate ; repeat foo'.
*)
Qed.
  
Lemma prog2_div : forall s1 s2, eval_com prog2 s1 s2 -> False.

  Lemma prog2_div' : forall c s1 s2, eval_com c s1 s2 -> c = prog2 -> False.
  Proof.
    unfold prog2 ; induction 1; crush.
  Qed.
  Show.
  intros. apply (prog2_div' _ _ _ H eq_refl).
Qed.

(** A simple chained tactic *)
Ltac myinv' H := inversion H ; subst ; clear H ; simpl in *.

(** This tactic applies when we have a hypothesis involving
   eval_com of either a Seq or an Assign.  It inverts the
   hypothesis, and performs substitution, simplifying things.
*)
Ltac eval_inv := 
  match goal with 
    | [ H : eval_com (Seq _ _) _ _ |- _ ] => myinv H
    | [ H : eval_com (Assign _ _) _ _ |- _ ] => myinv H
  end.

(** This tactic inverts an eval_com of a While, producing
   two sub-goals.  It tries to eliminate one (or both) of the goals
   through discrimination on the hypotheses.
*)
Ltac eval_while_inv := 
  match goal with
    | [ H : eval_com (While _ _) _ _ |- _ ] => myinv H ; try discriminate
  end.

Theorem prog1_prop' : forall s1 s2, eval_com prog1 s1 s2 -> get "x" s2 = 0.
Proof.
  unfold prog1 ; intros.
  repeat ((repeat eval_inv) ; eval_while_inv).
  auto.
Qed.

Theorem seq_assoc' : 
  forall c1 c2 c3 s1 s2, 
    eval_com (Seq (Seq c1 c2) c3) s1 s2 -> 
    eval_com (Seq c1 (Seq c2 c3)) s1 s2.
  Lemma seq_assoc'' : 
    forall c s1 s2, 
      eval_com c s1 s2 -> 
      forall c1 c2 c3,
        c = Seq (Seq c1 c2) c3 -> 
        eval_com (Seq c1 (Seq c2 c3)) s1 s2.
  Proof.
    (** Adds all of the eval_com constructors as hints for auto/crush *)
    Hint Constructors eval_com.
    induction 1 ; crush.
    inversion H ; clear H ; subst ; 
    econstructor ; eauto.
  Qed.

  intros. eapply seq_assoc'' ; eauto.
Qed.

(** Returns true when the variable x occurs as a subexpression of a *)
Fixpoint contains (x:var) (a:aexp) : bool := 
  match a with 
    | Const _ => false
    | Var y => if string_dec x y then true else false
    | Binop a1 _ a2 => contains x a1 || contains x a2
  end.

SearchAbout (or).
(** Changing a variable x that doesn't occur in a doesn't effect the 
   value of a. *)
Lemma eval_exp_set : 
  forall s x n a,
    contains x a = false -> 
    eval_aexp a (set x n s) = eval_aexp a s.
Proof.
  induction a.
  - intros. simpl. reflexivity.
  - intros. simpl. myinv H. unfold set. unfold get. destruct (string_dec x v).
   + discriminate.
   + reflexivity.
  - intros. myinv H. SearchAbout (_ || _ = false). 
    apply orb_false_elim in H1. destruct H1. apply IHa1 in H. rewrite H.
    apply IHa2 in H0. rewrite H0. reflexivity.

(** Greg'g Proof
destruct H1. eapply (or_introl ) in IHa1. destruct IHa1.
    + Print or_intror . apply (or_intror (contains x a1 = contains x a1)).
  induction a ; unfold set, get ; simpl ; unfold get ; crush.
  destruct (string_dec x v) ; crush.
  destruct (contains x a1) ; crush.
*)
Qed.

(** 
Problem Set 3
In class we saw a relational small-step semantics for IMP. 
Abhishek observed that the small-step semantics could be written
as a function instead, since there is no recursion in the 'while' case.
However, there is a loss of extensibility to some nondeterministic
 features like concurrency.) Are these semantics really equivalent?
Here is the relational semantics we saw in class:

*)

Inductive step_com : com -> state -> com -> state -> Prop := 
| Step_assign: forall s x e,
       step_com (Assign x e) s
                (Skip) (set x (eval_aexp e s) s)
| Step_seqL: forall c1 c2 c1' s s', step_com c1 s c1' s' ->
                step_com (Seq c1 c2) s (Seq c1' c2) s'
| Step_seqR: forall c s, step_com (Seq Skip c) s c s
| Step_if_true: forall b c1 c2 s, eval_bexp b s = true ->
                 step_com (If b c1 c2) s c1 s
| Step_if_false: forall b c1 c2 s, eval_bexp b s = false ->
                 step_com (If b c1 c2) s c2 s
| Step_while: forall b c s,
                 step_com (While b c) s
                          (If b (Seq c (While b c)) Skip) s.

SearchAbout (Some ).
(** Problem1: Give a definition of the same small-step semantics,
 as a function.
*)

Fixpoint  step_com_fn  (c: com) (s: state) : option (com * state) :=
  match c with 
    | Skip => None
    | Assign v a => Some (Skip, (set v (eval_aexp a s) s))
    | Seq c1 c2 => match (step_com_fn c1 s) with 
                    | None => Some (c2, s) (** this is skip case*)
                    | Some (c3, s1) => Some ((Seq c3 c2), s1)
                   end
    | If b c1 c2  => match eval_bexp b s with
                        | true => Some (c1, s)
                        | false => Some (c2, s)
                       end
    | While b c1 => match eval_bexp b s with
                      | true => Some ((Seq c1 c), s)
                      | false => Some (Skip, s)
                    end
   end.


(** Prove that only Skip fails to step: *)
Lemma progress : forall c s, step_com_fn c s = None -> c = Skip.
Proof.
  intro c.
  induction c.
(** ; intros; simpl in *; try( reflexivity); try (discriminate). *)
  - intros. reflexivity. (**skip case*)
  - intros. simpl in *. discriminate. (**Assign case*)
  (**Seq case*)
  - simpl in *. intros. destruct (step_com_fn c1 s) in H.
    + destruct p. discriminate.
    + discriminate.
  - simpl in *. intros. destruct (eval_bexp b s) in H; discriminate.
  - simpl in *. intros. remember ((eval_bexp b s)) as bb. 
      destruct bb. 
    + inversion H.
    + discriminate.
Qed.


Lemma ss {A:Type} : forall (a b:A), Some a= Some b -> a =b.
Proof using.
  intros. inversion H. reflexivity.
Qed.


(** Prove that all steps in the functional semantics work in the
   relational one.*) 
Theorem forward_sim : forall c s c' s', 
          step_com_fn c s = Some (c', s') -> step_com c s c' s'.
Proof.
 intro c. induction c.
 * intros. simpl in *. discriminate.
 * intros. simpl in *. myinv H. constructor.
 * intros. simpl in *. remember (step_com_fn c1 s) as ss.
   destruct ss.
  + destruct p. myinv H. constructor. apply IHc1. 
    symmetry in Heqss. assumption.
  + inversion H. symmetry in Heqss. 
    apply progress in Heqss. subst. constructor.
 * intros. simpl in H. remember (eval_bexp b s) as bb.
   destruct bb; myinv H; symmetry in Heqbb; constructor; apply Heqbb.
 * intros. simpl in H. Print step_com. remember (eval_bexp b s) as bb.
   destruct bb.
   + myinv H. symmetry in Heqbb. Print step_com. 
     remember (Seq c (While b c)) as if_st. apply (If b (Seq c (While b c)) Skip) .  
     apply (If b (Seq c (While b c)) Skip) in Heqif_st. 
     
     assert (If b (Seq c (While b c)) Skip).


(** We can commute assignments x:=ax; y:=ay  as long as the 
   variables don't overlap. *)
Lemma assign_comm : 
  forall x ax y ay s1 s2,
    eval_com (Seq (Assign x ax) (Assign y ay)) s1 s2 -> 
    contains x ay = false -> 
    contains y ax = false -> 
    x <> y -> 
    forall s3, eval_com (Seq (Assign y ay) (Assign x ax)) s1 s3 -> s2 = s3..
(*
               forall z, get z s3 = get z s2.
*)
Proof.
  
  intros.
  repeat eval_inv.
  repeat unfold set, get.
  destruct (string_dec x z) ; destruct (string_dec y z) ; try congruence.
  specialize (eval_exp_set s1 y (eval_aexp ay s1) ax H1).
  unfold set. crush.
  specialize (eval_exp_set s1 x (eval_aexp ax s1) ay H0).
  unfold set. crush.
Qed.


Lemma assign_comm2 : 
  forall x ax y ay s1 s2,
    eval_com (Seq (Assign x ax) (Assign y ay)) s1 s2 -> 
    contains x ay = false -> 
    contains y ax = false -> 
    x <> y -> 
    eval_com (Seq (Assign y ay) (Assign x ax)) s1 s2.
Proof.
  intros.
  remember (set x (eval_aexp ax (set y (eval_aexp ay s1) s1))
                (set y (eval_aexp ay s1) s1)) as s3.
  assert (eval_com (Seq (Assign y ay) (Assign x ax)) s1 s3).
  rewrite Heqs3.
  eauto.
  specialize (assign_comm x ax y ay s1 s2 H H0 H1 H2 _ H3).
  intro.
  assert (s3 = s2).
  Focus 2.
  rewrite <- H5.
  auto.
  Admitted.