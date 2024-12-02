/*
Lecture #4: recursive specification / iterative implementation

with inspiration from Rustan Leino's "Basics of specification and verification: Lecture 1, loop invariants": https://www.youtube.com/watch?v=J0FGb6PyO_k

*/
method Main() {
	// 0 1 1 2 3 5 8 13 21 34 55 ...
	var x := ComputeFib(7); // method call: the returned value of "b" will be assigned into the local "x"
	assert x == Fib(7) == Fib(5)+Fib(6);
	print "The Fibonacci number of 7 is ";
	print x;

	x := ComputeFib(1_000_000);
	assert x == Fib(1_000_000) == Fib(999_998) + Fib(999_999);
	print "The Fibonacci number of 1_000_000 is ";
	print x;
}

ghost function Fib(n: nat): nat
	decreases n
{
	if n == 0 then 0 else if n == 1 then 1 else Fib(n-2) + Fib(n-1)
}

ghost predicate Inv(n: nat, i: nat, a: nat, b: nat) { 2 <= i <= n && a == Fib(i-1) && b == Fib(i) }

method ComputeFib'(n: nat) returns (b: nat)
	ensures b == Fib(n)
{
	if n < 2	{
		b := n;
		return;
	}
	var i, a;
	a, b, i := 1, 1, 2;
	while i != n
		invariant Inv(n, i, a, b)
	{
		a, b := b, a+b;
		i := i+1;
	}
}

method ComputeFib(n: nat) returns (b: nat)
	ensures b == Fib(n)
{
	if n < 2	{
		assert n < 2;
		LemmaBaseCase(n); // ==> // recall that 0 <= n by the type "nat" so we have here only two cases: 0 and 1
		assert n == Fib(n);
		b := n;
		assert b == Fib(n);
		return;
	}
	assert 2 <= n;
	LemmaInit(n); // ==>
	assert Inv(n, 2, 1, 1); // 0 <= 2 <= n && 1 == Fib(1) && 1 == Fib(2)
	var i, a;
	a, b, i := 1, 1, 2;
	assert Inv(n, i, a, b);
	while i != n
		invariant Inv(n, i, a, b)
		decreases n-i
	{
		assert Inv(n, i, a, b);
		assert i != n;
		LemmaInLoopBody(n, i, a, b);
		assert Inv(n, i+1, b, a+b);
		assert 0 <= n-(i+1) < n-i;
		ghost var V0 := n-i;
		assert Inv(n, i+1, b, a+b); // b == Fib(i) && a+b == Fib(i+1) == Fib(i-1)+Fib(i)
		assert 0 <= n-(i+1) < V0;
		a, b := b, a+b; // multiple assignmet, also known as "simultaneous assignment" or "parallel assignment" or "let assignment"
		i := i+1;
		assert Inv(n, i, a, b);
		assert 0 <= n-i < V0;
	}
	assert Inv(n, i, a, b) && i == n;
	LemmaPostcondition(n, i, a, b); // ==>
	assert b == Fib(n);
}

lemma LemmaInLoopBody(n: nat, i: nat, a: nat, b: nat)
	requires Inv(n, i, a, b)
	requires i != n
	ensures Inv(n, i+1, b, a+b)
	ensures 0 <= n-(i+1) < n-i
{}

lemma LemmaBaseCase(n: nat)
	requires n < 2
	ensures n == Fib(n)
{}

lemma LemmaInit(n: nat)
	requires 2 <= n
	ensures Inv(n, 2, 1, 1)
{}

lemma LemmaPostcondition(n: nat, i: nat, a: nat, b: nat)
	requires Inv(n, i, a, b)
	requires i == n
	ensures b == Fib(n)
{}
