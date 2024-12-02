/*
	Part A (12%)

	Goal:

	Complete the definition of the program entities below:
	"Guard1", "Inv1", "V1", "Init1", "LoopBody1" and "Lemma1",
	by providing a body, such that the methods ("Init1" and "LoopBody1")
	and the lemma ("Lemma1") will be verifiably correct.

	No need to document the proof obligations.

*/
predicate method Guard1(n: int, a: int)
	requires Inv1(n, a)

predicate Inv1(n: int, a: int)

function V1(a: int): int

method Init1(n: int) returns (a: int)
	requires n >= 0
	ensures Inv1(n, a)

method LoopBody1(n: int, a0: int) returns (a: int)
	requires Inv1(n, a0) && Guard1(n, a0)
	ensures Inv1(n, a) && 0 <= V1(a) < V1(a0)

lemma Lemma1(n: int, a: int)
	requires Inv1(n, a) && !Guard1(n, a)
	ensures a*a <= n && n < (a+1)*(a+1)

method Sqrt_Down_Loop(n: int) returns (a: int)
	requires n >= 0
	ensures a*a <= n && n < (a+1)*(a+1)
{
	a := Init1(n);
	while Guard1(n, a)
		invariant Inv1(n, a)
		decreases V1(a)
	{
		a := LoopBody1(n, a);
	}
	Lemma1(n, a);
}

/*
	Part B (13%)

	Goal:

	Complete the definition of the program entities below:
	"Guard2", "Inv2", "V2", "Init2", "LoopBody2" and "Lemma2",
	by providing a body, such that the methods ("Init2" and "LoopBody2")
	and the lemma ("Lemma2") will be verifiably correct.

	No need to document the proof obligations.

	Restriction:

	Both methods should be implemented with assignment statements only.

*/
function Fib(n: nat): nat
	decreases n
{
	if n == 0 then 0 else if n == 1 then 1 else Fib(n-2) + Fib(n-1)
}

predicate method Guard2(n: nat, i: nat, a: nat, b: nat)
	requires Inv2(n, i, a, b)

predicate Inv2(n: nat, i: nat, a: nat, b: nat)

function V2(n: nat, i: nat, a: nat, b: nat): int

method Init2(n: nat) returns (i: nat, a: nat, b: nat)
	ensures Inv2(n, i, a, b)

method LoopBody2(n: nat, i0: nat, a0: nat, b0: nat) returns (i: nat, a: nat, b: nat)
	requires Inv2(n, i0, a0, b0) && Guard2(n, i0, a0, b0)
	ensures Inv2(n, i, a, b) && 0 <= V2(n, i, a, b) < V2(n, i0, a0, b0)

lemma Lemma2(n: nat, i: nat, a: nat, b: nat)
	requires Inv2(n, i, a, b) && !Guard2(n, i, a, b)
	ensures a == Fib(n)

method ComputeFib2(n: nat) returns (a: nat)
	ensures a == Fib(n)
{
	var i: nat, b: nat;
	i, a, b := Init2(n);
	while Guard2(n, i, a, b)
		invariant Inv2(n, i, a, b)
		decreases V2(n, i, a, b)
	{
		i, a, b := LoopBody2(n, i, a, b);
	}
	Lemma2(n, i, a, b);
}

predicate ValidTimeOfDay(h: int, m: int) { 0 <= h < 24 && 0 <= m < 60 }

/*
	Part C (50%)

	Goal:

	Implement correctly, using a "while" loop, **documenting the proof obligations**
	as we've learned, with assertions and a lemma for each proof goal.

	Restriction:

	The only arithmetic operations allowed in your *code* are addition and subtraction,
	whereas other operations (such as multiplication, division, or modulo) may be used
	in *specification contexts* only (such as assertions and loop invariants).

*/
method TimeOfDay(minutes_since_midnight: int) returns (h: int, m: int)
	requires 0 <= minutes_since_midnight < 24*60
	ensures h*60+m == minutes_since_midnight
	ensures ValidTimeOfDay(h, m)

/*
	Part D (25%)

	Goal: Implement correctly. No need to document the proof obligations.

	Restriction:

	Again, the only arithmetic operations allowed in your *code* are addition and subtraction,
	whereas other operations (such as multiplication, division, or modulo) may be used
	in *specification contexts* only (such as assertions and loop invariants).

*/
method UpdateTime(start_h: int, start_m: int, minutes: int) returns (d: int, h: int, m: int)
	requires ValidTimeOfDay(start_h, start_m)
	ensures ValidTimeOfDay(h, m)
	ensures start_h*60 + start_m + minutes == d*24*60 + h*60 + m
