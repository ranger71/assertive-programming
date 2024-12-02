/*
Lecture #5: one more example of recursive specification / iterative implementation + proofs in Dafny + a first program with sequences of integers

- In "ComputeFactorial2", using a "down loop", we could see an alternative approach to the design of a loop invariant,
  focusing on the gap between what's been already computed and the expected value
- As an introduction for proofs in Dafny we reviewed some examples from Chapter 5 of Leino's "Program Proofs" (see https://program-proofs.com/code.html)
- Sequences are read-only (immutable) arrays. We'll later work with arrays too. In such programs we may still want to work with sequences,
  in the annotation, for expressing the proog obligations. This is why we first learn how to work with sequences.
- We also discuss the notion of "infeasible" specifications: for a specification to be feasible we need for each valid initial state
  to be guaranteed to have at least one possible final state that satisfies the postcondition
*/
function factorial(n: int): int
	requires n >= 0
	decreases n
{
	if n == 0 then 1 else n*factorial(n-1)
}

method ComputeFactorial(n: int) returns (f: int)
	requires n >= 0
	ensures f == factorial(n)
{
	var i;
	f, i := 1, 0;
	while i != n
		invariant 0 <= i <= n
		invariant f == factorial(i)
		decreases n-i
	{
		f, i := f*(i+1), i+1;
	}
}

method ComputeFactorial2(n: int) returns (f: int)
	requires n >= 0
	ensures f == factorial(n)
{
	var i;
	f, i := 1, n;
	while i != 0
		invariant 0 <= i <= n
		invariant f*factorial(i) == factorial(n)
		decreases i
	{
		f := f*i;
		i := i-1;
	}
}

method Search'(q: seq<int>, key: int) returns (i: nat)
	requires key in q
	ensures i < |q| && q[i] == key
{
	i := 0;
	while q[i] != key
		invariant i < |q| && key in q[i..]
		decreases |q|-i
	{
		i := i+1;
	}
}

// the precondition is needed here, otherwise the program would be "infeasible"
method {:verify true} Search(q: seq<int>, key: int) returns (i: nat)
	requires key in q // syntactic sugar for (exists i :: 0 <= i < |q| && q[i] == key)
	ensures i < |q| && q[i] == key
{
	assert key in q;
	LemmaInit(q, key); // ==>
	assert 0 < |q| && key in q[0..];
	i := 0;
	assert i < |q| && key in q[i..];
	while q[i] != key
		invariant i < |q| && key in q[i..]
		decreases |q|-i
	{
		assert i < |q| && key in q[i..];
		assert q[i] != key;
		LemmaLoopBody(q, key, i); // ==>
		assert i+1 < |q| && key in q[i+1..];
		assert 0 <= |q|-(i+1) < |q|-i;
		ghost var V0 := |q|-i;
		assert i+1 < |q| && key in q[i+1..];
		assert 0 <= |q|-(i+1) < V0;
		i := i+1;
		assert i < |q| && key in q[i..];
		assert 0 <= |q|-i < V0;
	}
	assert i < |q| && key in q[i..];
	assert !(q[i] != key);
	LemmaPost(q, key, i); // ==>
	assert i < |q| && q[i] == key;

	/* instead of the above, would this work? if so, what would be the invariant that will make it verifiable?
	i := 0;
	while true
		invariant i < |q| && ???
	{
		if q[i] == key
		{
			return i;
		}
		i := i+1;
	}
	*/
}

lemma LemmaInit(q: seq<int>, key: int)
	requires key in q
	ensures 0 < |q| && key in q[0..]
{}

lemma LemmaLoopBody(q: seq<int>, key: int, i: nat)
	requires i < |q| && key in q[i..]
	requires q[i] != key
	ensures i+1 < |q| && key in q[i+1..]
	ensures 0 <= |q|-(i+1) < |q|-i
{}

lemma LemmaPost(q: seq<int>, key: int, i: nat)
	requires i < |q| && key in q[i..]
	requires !(q[i] != key)
	ensures i < |q| && q[i] == key
{}

method Main() {
	var f;
	f := ComputeFactorial(3);
	assert f == 6;
	print "3! = ";
	print f;
	print "\n";
	f := ComputeFactorial(4);
	assert f == 24;
	print "4! = ";
	print f;
	print "\n";
	f := ComputeFactorial(5);
	assert f == 120;
	print "5! = ";
	print f;
	print "\n";

	var i := Search([9,7,8,7], 7);
	assert i == 1 || i == 3;
	print "[9,7,8,7][";
	print i;
	print "] = 7\n";

	i := Search([4], 4);
	assert i == 0;
	print "[4][";
	print i;
	print "] = 4\n";

	// prefixes, suffixes, and concatenation of sequences:
	assert forall q: seq<int>,i :: 0 <= i <= |q| ==> q[..i] + q[i..] == q;
}
