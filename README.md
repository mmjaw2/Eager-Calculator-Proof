# Eager Calculator Proof
A proof, proving that an eager calculator works the same as a normal calculator for all supported expressions and on all inputs.

## What is an Eager Calculator?
Eager calculators, also sometimes referred to as partial calculators or evaluators, take incomplete expressions and simplifies them so as to look less complex while being logically equivalent to the original expression. This matters with, in this project's case, algebraic expressions that have variables. Eager calculators can simplify algebraic expressions that have unassigned variables so as to take less memory in storage whilst, ofcourse, staying logically correct.

Here is an example of an eagerly evaluated expression:
``` 3*(x + 2) * 6 which simplifies to 18 * x + 54```
The above expression when simplified contains less operators and less values that the program will need to keep track of. Whereas a normal calculator will hold on to the original expression until an input for x is given.

Eager calculators become especially tricky when dealing with commutative, associative, and distributive rules:

``` x + 2 = 2 + x```

```1 + x + y = y + 1 + x```

```2*(x + y) = 2*x + 2*y```

All of these expressions above are tricky to implement. I cover how I did it in a later section in this write-up. 

## Inspiration for this project
Last semester, Fall of 2024, I took a language design class that had me implement a complex eager calculator for fuzzy logic. In that project, the fuzzy logic eager calculator dealt with very unsafe procedures like using mutable maps, making temporary global variables, and such. Coming out of that class, I thought that proving the correctness of an eager calculator would be a fun challenge that ties back to language design. In this project, instead of dealing with fuzzy logic, I decided to prove a normal algebraic eager calculator but used much of the fuzzy logic code as a reference. Hopefully, in the future, I'll expand on this project and prove the eager calculator for fuzzy logic.

# General Mechanical Overview
```Coq
  Theorem EqualEval: forall e: Expression, forall inputs: list Input,
	  Eval e inputs = Eval (EagerEval e) inputs.
```
The above is the theorem I set out to prove starting this project. It simply means that for all expressions and for all inputs, running the expression through the eager evaluator before-hand, will still yield the same result as the original expression.

The general theorem called for a basic implementation of the following:
- An expression system
- An input system
- A normal evaluator
- The eager evaluator (of course)

## Expression System
Below is the expression system source code. It holds basic capabilities of making recursive expressions like Add( Add ( Add ( Add (1 2) 3) 4) 5). The expression system runs on real numbers so that division could be done.
```Coq
Inductive Expression :=
	| Val(x : R) : Expression
	| Var(s : string) : Expression
	|	Add(x y : Expression) : Expression
	|	Subtract(x y : Expression) : Expression
	|	Multiply(x y : Expression) : Expression
	|	Divide(x y : Expression) : Expression.
```

## Input System
The input system uses a Record "Input" to store a pair of values, a string and a value. The pair of values makes searching for values based on the name possible- so if there is "x" in an expression, "x" can be mapped to a value. The searching mechanism is handled by GetInput, which takes a string and a list of Inputs, searches the list of Inputs for any Input that has a matching "name" to the given string and returns the value found in the Input. Or if no value is found returns 0.
``` Coq
Record Input := {
	name : string;
	value : R;
}.

Fixpoint GetInput (nameInput : string) (inputs : list Input): R :=
	match inputs with
	| nil			=> 0%R
	| h :: t	=> if (String.eqb nameInput (name h)) then value h else GetInput nameInput t
	end.
```

Designing the Expression system and Input system like this, enables for a flexible system that can have dynamic inputs while not needing to change the expression.

## The Normal Evaluator
This is pretty simple, it takes an expression and a list of inputs, substitutes any inputs found in the expression, evaluates the expression and returns the result. The r_ functions do what they're advertised to do on real numbers, r_Add adds 2 real numbers, r_Subtract subtracts 2 real numbers and so on. A key detail here is that Eval is recursive, allowing for powerful compact statements.
```Coq
Fixpoint Eval (expr : Expression) (inputs : list Input): R :=
	match expr with
	| Val x					=> x
	| Var x					=> GetInput x inputs
	| Add x y 			=> r_Add (Eval x inputs) (Eval y inputs)
	| Subtract x y	=> r_Subtract (Eval x inputs) (Eval y inputs)
	| Multiply x y	=> r_Multiply (Eval x inputs) (Eval y inputs)
	| Divide x y		=> r_Divide (Eval x inputs) (Eval y inputs)
	end.
```

## The Eager Evaluator
This is the meat and potatoes of this project. In contrast to the normal eval, eagerEval returns an Expression of hopefully a simpler form. Whether the expression gets simplified is mainly dictated by the operation found. The basic logic is as follows- if an operation is found with values passed in, we know that the operation can be simplified to a value by executing the operation. For double Add and Multiply, if a mix of values and variables is found we can apply the associative and commutative rules to add the values while keeping variables separate (see the source code below). Lastly, if 2 variables are detected in Add and Multiply, we can freely move them however we want. An important note is that this moving on 2 variables is important to pass the commutative rule. I chose to order the variables in alphabetical order.
```Coq
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
```

# Proofs
When it comes to proofs, please take a look at the eager_calc.v file. Early in the file, I cover some basic proofs like basic expression evaluations without variables. Then some basic expressions with variables to make sure that commutative and associative rules hold. I have not implemented the distributive rule because the distributive rule relies on parentheses and this language does not support parenthesis. The end of the file covers the main theorem and a version of the theorem that does not take any inputs (I thought that the two theorem would have different proofs, but they did not).

# Future Notes
This project is officially done. I can't think of any significant rules that I have not covered. Expanding this project to support parenthesis is out of the current scope since that will require some language processing in a way that I don’t know if normal Coq supports. If I were to take this project to the next level, it would be a whole different project that includes the fuzzy logic I mentioned earlier.
