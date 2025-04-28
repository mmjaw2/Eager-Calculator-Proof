Require Import Nat.
Require Import Reals.
Require Import String.
Require Import List.

Lemma add_custom1: forall x y z : R,
	(x + (y + z))%R = (z + (x + y))%R.
Proof.
	intros.
	rewrite Rplus_comm.
	symmetry.
	rewrite Rplus_comm.
	rewrite Rplus_assoc.
	apply Rplus_comm.
Qed.

Lemma add_custom2: forall x y z : R,
	(x + (y + z))%R = (y + (x + z))%R.
Proof.
	intros.
	rewrite Rplus_comm.
	symmetry.
	rewrite Rplus_comm.
	ring.
Qed.

Definition IsEarlier (s1 s2 : string) : bool :=
  match String.compare s1 s2 with
  | Lt => true
  | _ => false
  end.

Definition r_Add (x y : R) : R := x + y.

Definition r_Subtract (x y : R) : R := x - y.

Definition r_Multiply (x y : R) : R := x * y.

Definition r_Divide (x y : R) : R := x / y.

Inductive Expression :=
	| Val(x : R) : Expression
	| Var(s : string) : Expression
	|	Add(x y : Expression) : Expression
	|	Subtract(x y : Expression) : Expression
	|	Multiply(x y : Expression) : Expression
	|	Divide(x y : Expression) : Expression.

Record Input := {
	name : string;
	value : R;
}.

Fixpoint GetInput (nameInput : string) (inputs : list Input): R :=
	match inputs with
	| nil			=> 0%R
	| h :: t	=> if (String.eqb nameInput (name h)) then value h else GetInput nameInput t
	end.

Fixpoint Eval (expr : Expression) (inputs : list Input): R :=
	match expr with
	| Val x					=> x
	| Var x					=> GetInput x inputs
	| Add x y 			=> r_Add (Eval x inputs) (Eval y inputs)
	| Subtract x y	=> r_Subtract (Eval x inputs) (Eval y inputs)
	| Multiply x y	=> r_Multiply (Eval x inputs) (Eval y inputs)
	| Divide x y		=> r_Divide (Eval x inputs) (Eval y inputs)
	end.

Fixpoint EagerEval (expr : Expression): Expression :=
	match expr with
	| Val x					=> 	Val x
	|	Var x					=> 	Var x
	| Add x y 			=> 	match (EagerEval x, EagerEval y) with
											| (Val a, Val b) 									=> Val (a+b)
											| (Add (Val a) (Var b), Val c)		=> Add (Var b) (Val (a+c))
											| (Add (Var a) (Val b), Val c)		=> Add (Var a) (Val (b+c))
											|	(Val a, Add (Val b) (Var c))		=> Add (Var c) (Val (a+b))
											| (Val a, Add (Var b) (Val c))		=> Add (Var b) (Val (a+c))
											| (Val a, _)											=> Add y (Val a)
											| (_, Val b)											=> Add x (Val b)
											| (Var a, Var b)									=> if (IsEarlier a b) then Add (Var a) (Var b) else Add (Var b) (Var a)
											| (_,_)														=> Add x y
											end
	| Subtract x y	=> 	match (EagerEval x, EagerEval y) with
											| (Val a, Val b)	=> Val (a-b)
											|	(_, _)					=> Subtract x y
											end
	| Multiply x y	=>	match (EagerEval x, EagerEval y) with
											| (Val a, Val b)											=> Val (a*b)
											| (Multiply (Val a) (Var b), Val c)		=> Multiply (Var b) (Val (a*c))
											| (Multiply (Var a) (Val b), Val c)		=> Multiply (Var a) (Val (b*c))
											|	(Val a, Multiply (Val b) (Var c))		=> Multiply (Var c) (Val (a*b))
											| (Val a, Multiply (Var b) (Val c))		=> Multiply (Var b) (Val (a*c))
											| (Val a, _)													=> Multiply y (Val a)
											| (_, Val b)													=> Multiply x (Val b)
											| (Var a, Var b)											=> if (IsEarlier a b) then Multiply (Var a) (Var b) else Multiply (Var b) (Var a)
											| (_,_)																=> Multiply x y
											end
	| Divide x y		=>	match (EagerEval x, EagerEval y) with
											| (Val a, Val b)	=> Val (a/b)
											| (_,_)						=> Divide x y
											end
	end.

Theorem add_comm: forall x y : R, r_Add x y = r_Add y x.
Proof.
	intros.
	unfold r_Add.
	apply Rplus_comm.
Qed.

Theorem mult_comm : forall x y : R, r_Multiply x y = r_Multiply y x.
Proof.
	intros.
	unfold r_Multiply.
	apply Rmult_comm.
Qed.

(* Testing Eval *)
Compute Eval (Val 1%R) nil.
Compute Eval (Add (Val 1%R) (Val 2%R)) nil.

(* Testing Eval with variable inputs *)
Definition my_inputs := (Build_Input "x" 3%R) :: (Build_Input "y" 1%R) :: nil.
Compute Eval (Add (Var "x") (Var "y")) (my_inputs).

(* Testing EagerEval *)
(* (1 + 1) *)
Definition expr1: Expression := Add (Val 1%R) (Val 1%R).
Compute EagerEval expr1.

(* ((1 + 1) + 1) *)
Definition expr2: Expression := Add (Add (Val 1%R) (Val 1%R)) (Val 1%R).
Compute EagerEval expr2.

(* 2 * 2 *)
Definition expr3 := Multiply (Val 2%R) (Val 2%R).
Compute EagerEval expr3.

(* (2 * (2 + (4 - 3))) / 2 *)
Definition expr4 := Divide (Multiply (Val 2%R) (Add (Val 2%R) (Subtract (Val 4%R) (Val 3%R)))) (Val 2%R).
Compute EagerEval expr4.

(* 2 * x *)
Definition expr5 : Expression := Multiply (Val 2%R) (Var "x").
Compute EagerEval expr5.

(* 2 + 2 + x *)
Definition expr6 : Expression := Add (Val 2%R) (Add (Val 2%R) (Var "x")).
Compute EagerEval expr6.

(* 2 + x + 2 *)
Definition expr7 : Expression := Add (Val 2%R) (Add (Var "x") (Val 2%R)).
Compute EagerEval expr7.

Theorem simple_addition : EagerEval expr6 = EagerEval expr7.
Proof.
	simpl. reflexivity.
Qed.

(* 2 * (3 * x) *)
Definition expr8 : Expression := Multiply (Val 2%R) (Multiply (Val 3%R) (Var "x")).

(* 2 * (x * 3) *)
Definition expr9 : Expression := Multiply (Val 2%R) (Multiply (Var "x") (Val 3%R)).

(* x * (3 * 2) *)
Definition expr10 : Expression := Multiply (Var "x") (Multiply (Val 3%R) (Val 2%R)).

Theorem simple_multiplication : EagerEval expr8 = EagerEval expr9.
Proof.
	simpl. reflexivity.
Qed.

Theorem simple_multiplication2 : EagerEval expr9 = EagerEval expr10.
Proof.
	simpl. rewrite Rmult_comm. reflexivity.
Qed.

(* Division over 0 *)
Definition expr11 : Expression := Divide (Val 1%R) (Val 0%R).
Compute EagerEval expr11.

(* Expression with no Variables yields the same result when eagerly evaluated as normal eval *)
Theorem expr4_test:
	Eval expr4 nil = Eval (EagerEval expr4) nil.
Proof.
	simpl.
	unfold r_Subtract.
	unfold r_Add.
	unfold r_Multiply.
	unfold r_Divide.
	reflexivity.
Qed.

(* 2 + x = x + 2 *)
Lemma comm_add_test:
	EagerEval (Add (Val 2%R) (Var "x")) = EagerEval (Add (Var "x") (Val 2%R)).
Proof.
	simpl.
	reflexivity.
Qed.

(* x + y = y + x *)
Lemma comm_add_test_2:
	EagerEval (Add (Var "x") (Var "y")) = EagerEval (Add (Var "y") (Var "x")).
Proof.
	simpl.
	reflexivity.
Qed.

(* 2 * x = x * 2 *)
Lemma comm_mult_test:
	EagerEval (Multiply (Val 2%R) (Var "x")) = EagerEval (Multiply (Var "x") (Val 2%R)).
Proof.
	simpl.
	reflexivity.
Qed.

(* x * y = y * x *)
Lemma comm_mult_test_2:
	EagerEval (Multiply (Var "x") (Var "y")) = EagerEval (Multiply (Var "y") (Var "x")).
Proof.
	simpl.
	reflexivity.
Qed.

Theorem EqualEvalNoInputs: forall e : Expression,
	Eval e nil = Eval (EagerEval e) nil.
Proof.
	intros.
	induction e.
	- simpl. reflexivity.
	- simpl. reflexivity.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Add; rewrite IHe1, IHe2; simpl;
		try reflexivity; try apply Rplus_comm; unfold r_Add;
		try destruct e3; try destruct e4; simpl; try rewrite IHe1, IHe2;
		try reflexivity; try rewrite IHe2; unfold r_Add; simpl;
		unfold r_Add; simpl; try ring; try rewrite IHe1; simpl;
		unfold r_Add; try ring.
		unfold IsEarlier; destruct (s ?= s0)%string;
		simpl; unfold r_Add; simpl; reflexivity.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Add; simpl; rewrite IHe1, IHe2; simpl; reflexivity.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Multiply; rewrite IHe1, IHe2; simpl;
		try reflexivity; try apply Rmult_comm; unfold r_Multiply;
		try destruct e3; try destruct e4; simpl; try rewrite IHe1, IHe2;
		try reflexivity; try rewrite IHe2; unfold r_Multiply; simpl;
		unfold r_Multiply; simpl; try ring; try rewrite IHe1; simpl;
		unfold r_Multiply; try ring.
		unfold IsEarlier; destruct (s ?= s0)%string;
		simpl; unfold r_Add; simpl; reflexivity.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Add; simpl; rewrite IHe1, IHe2; simpl; reflexivity.
Qed.

Theorem EqualEval: forall e: Expression, forall inputs: list Input,
	Eval e inputs = Eval (EagerEval e) inputs.
Proof.
	intros.
	induction e.
	- simpl. reflexivity.
	- simpl. reflexivity.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Add; rewrite IHe1, IHe2; simpl;
		try reflexivity; try apply Rplus_comm; unfold r_Add;
		try destruct e3; try destruct e4; simpl; try rewrite IHe1, IHe2;
		try reflexivity; try rewrite IHe2; unfold r_Add; simpl;
		unfold r_Add; simpl; try ring; try rewrite IHe1; simpl;
		unfold r_Add; try ring.
		unfold IsEarlier; destruct (s ?= s0)%string;
		simpl; unfold r_Add; simpl; try reflexivity;
		apply Rplus_comm.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Add; simpl; rewrite IHe1, IHe2; simpl; reflexivity.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Multiply; rewrite IHe1, IHe2; simpl;
		try reflexivity; try apply Rmult_comm; unfold r_Multiply;
		try destruct e3; try destruct e4; simpl; try rewrite IHe1, IHe2;
		try reflexivity; try rewrite IHe2; unfold r_Multiply; simpl;
		unfold r_Multiply; simpl; try ring; try rewrite IHe1; simpl;
		unfold r_Multiply; try ring.
		unfold IsEarlier; destruct (s ?= s0)%string;
		simpl; unfold r_Add; simpl; try reflexivity;
		apply Rmult_comm.
	- simpl.
		destruct (EagerEval e1) eqn:He1, (EagerEval e2) eqn:He2;
		simpl; unfold r_Add; simpl; rewrite IHe1, IHe2; simpl; reflexivity.
Qed.








