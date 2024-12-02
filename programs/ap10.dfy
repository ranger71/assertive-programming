// Distributive Operators (Morgan's PfS Section 9.4, Leino's PP Section 12.3): Sigma, Sum of Integers
method Main() {
	var a: array<int> := new int[4] [3,8,5,-1];
	print a[..];
	var sum := ComputeSum_1(a[..]);
	assert l1: sum == RecursiveSumUp(a[..]);
	print "\nThe sum of all elements in the array is: ";
	print sum;
	var sum2 := ComputeSum_2(a[..]);
	assert sum == sum2 by {
		calc {
			sum2;
		== // from the postcondition of ComputeSum_2
			RecursiveSumDown(a[..]);
		==	{ EquivalentSumDefinitions(a[..]); } // see at the end (proof by induction)
			RecursiveSumUp(a[..]);
		== { reveal l1; }
			sum;
		}
	}
}

// Distributive Operators: Sigma, Sum of Integers
ghost function RecursiveSumUp(q: seq<int>): int
	decreases |q|
{
	if q == [] then 0 else q[0]+RecursiveSumUp(q[1..])
}

ghost function RecursiveSumDown(q: seq<int>): int
	decreases |q|
{
	if q == [] then 0 else q[|q|-1]+RecursiveSumDown(q[..|q|-1])
}

// up loop
method ComputeSum_1'(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumUp(q)
{
	var i := 0;
	sum := 0;
	while i < |q|
		invariant 0 <= i <= |q| && sum == RecursiveSumUp(q[..i])
	{
		Lemma_1a(q, i, sum);
		sum := sum+q[i];
		i := i+1;
	}
	Lemma_1b(q, i, sum);
}

method ComputeSum_1(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumUp(q)
{
	var i := 0;
	sum := 0;
	while i < |q|
		invariant 0 <= i <= |q| && sum == RecursiveSumUp(q[..i])
		decreases |q|-i
	{
		assert 0 <= i < |q| && sum == RecursiveSumUp(q[..i]);
		Lemma_1a(q, i, sum);
		assert 0 <= i+1 <= |q| && sum+q[i] == RecursiveSumUp(q[..i+1]);
		sum := sum+q[i];
		assert 0 <= i+1 <= |q| && sum == RecursiveSumUp(q[..i+1]);
		i := i+1;
		assert 0 <= i <= |q| && sum == RecursiveSumUp(q[..i]);
	}
	assert 0 <= i <= |q| && sum == RecursiveSumUp(q[..i]);
	assert i >= |q|;
	Lemma_1b(q, i, sum);
	assert sum == RecursiveSumUp(q);
}

lemma Lemma_1a(q: seq<int>, i: nat, sum: int)
	requires pre1: 0 <= i < |q|
	requires pre2: sum == RecursiveSumUp(q[..i])
	ensures 0 <= i+1 <= |q| && sum + q[i] == RecursiveSumUp(q[..i+1])
{
	reveal pre1;
	assert q[..i+1] == q[..i] + [q[i]];
	var q1 := q[..i+1];
	calc {
		RecursiveSumUp(q[..i+1]);
	== // def.
		if q1 == [] then 0 else q1[0] + RecursiveSumUp(q1[1..]);
	== { assert q1 != []; } // simplification for a non-empty sequence
		q1[0] + RecursiveSumUp(q1[1..]);
	== // def. of q1
		q[0] + RecursiveSumUp(q[1..i+1]);
	== { PrependSumUp(q[..i+1]); }
		RecursiveSumUp(q[..i+1]);
	== { AppendSumUp(q[..i+1]); }
		RecursiveSumUp(q[..i]) + q[i];
	== { reveal pre2; } // precondition to the lemma
		sum + q[i];
	}
}

lemma Lemma_1b(q: seq<int>, i: nat, sum: int)
	requires inv: 0 <= i <= |q| && sum == RecursiveSumUp(q[..i])
	requires neg_of_guard: i >= |q|
	ensures sum == RecursiveSumUp(q)
{
	assert i <= |q| && sum == RecursiveSumUp(q[..i]) by { reveal inv; }
	assert i == |q| by { reveal inv,neg_of_guard; }
	assert q[..i] == q[..|q|] == q;
}

lemma PrependSumUp(q: seq<int>)
	requires q != []
	ensures RecursiveSumUp(q) == q[0] + RecursiveSumUp(q[1..])
{
	// directly from the definition of RecursiveSumUp (for a non-emty sequence)
}

// this is true, yet not in a trivial way, which explains why our first attempt is not easily proved by Dafny without manual help from us;
// this is our first proof by induction
lemma AppendSumUp(q: seq<int>)
	requires q != []
	ensures RecursiveSumUp(q) == RecursiveSumUp(q[..|q|-1]) + q[|q|-1]
	decreases |q|
{
	if |q| == 1
	{
		// base case
		assert RecursiveSumUp(q) == q[0] + RecursiveSumUp(q[1..]) == q[0] + RecursiveSumUp([]) == q[0] + 0 == q[0];
		assert q[0] == q[|q|-1] ==	0 + q[|q|-1] == RecursiveSumUp([]) + q[|q|-1] == RecursiveSumUp(q[..|q|-1]) + q[|q|-1];
	}
	else
	{
		// inductive step
		var q1 := q[1..];
		calc {
			RecursiveSumUp(q);
		== // def. for a non-empty sequence
			q[0] + RecursiveSumUp(q[1..]);
		== { assert q1 != []; assert |q1| < |q|; AppendSumUp(q1); } // induction hypothesis (one assertion for the precondition, another for termination)
			q[0] + RecursiveSumUp(q1[..|q1|-1]) + q1[|q1|-1];
		== { assert q1[..|q1|-1] == q[1..|q|-1]; assert q1[|q1|-1] == q[|q|-1]; }
			q[0] + RecursiveSumUp(q[1..|q|-1]) + q[|q|-1];
		== // def. for a non-empty sequence
			RecursiveSumUp(q[..|q|-1]) + q[|q|-1];
		}
	}
}

// up loop with the opposite definition in the postcondition and in the loop invariant, leading to a simpler to prove
method ComputeSum_2'(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumDown(q)
{
	var i := 0;
	sum := 0;
	while i < |q|
		invariant 0 <= i <= |q| && sum == RecursiveSumDown(q[..i])
	{
		assert q[..i+1] == q[..i]+[q[i]]; // Lemma_2a(q, i, sum);
		sum := sum+q[i];
		i := i+1;
	}
	assert q[..i] == q; // Lemma_2b(q, i, sum);
}

method ComputeSum_2(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumDown(q)
{
	var i := 0;
	sum := 0;
	while i < |q|
		invariant 0 <= i <= |q| && sum == RecursiveSumDown(q[..i])
		decreases |q|-i
	{
		assert 0 <= i < |q| && sum == RecursiveSumDown(q[..i]);
		Lemma_2a(q, i, sum);
		assert 0 <= i+1 <= |q| && sum+q[i] == RecursiveSumDown(q[..i+1]);
		sum := sum+q[i];
		assert 0 <= i+1 <= |q| && sum == RecursiveSumDown(q[..i+1]);
		i := i+1;
		assert 0 <= i <= |q| && sum == RecursiveSumDown(q[..i]);
	}
	assert 0 <= i <= |q| && sum == RecursiveSumDown(q[..i]);
	assert i >= |q|;
	Lemma_2b(q, i, sum);
	assert sum == RecursiveSumDown(q);
}

lemma Lemma_2a(q: seq<int>, i: nat, sum: int)
	requires 0 <= i < |q| && sum == RecursiveSumDown(q[..i])
	ensures 0 <= i+1 <= |q| && sum + q[i] == RecursiveSumDown(q[..i+1])
{
	var q1 := q[..i+1];
	calc {
		RecursiveSumDown(q[..i+1]);
	== // def.
		if q1 == [] then 0 else q1[|q1|-1] + RecursiveSumDown(q1[..|q1|-1]);
	== { assert q1 != []; } // simplification for a non-empty sequence
		q1[|q1|-1] + RecursiveSumDown(q1[..|q1|-1]);
	== { assert |q1|-1 == i; }
		q1[i] + RecursiveSumDown(q1[..i]);
	== { assert q1[..i] == q[..i]; }
		q[i] + RecursiveSumDown(q[..i]);
	== // inv.
		q[i] + sum;
	==
		sum + q[i];
	}
}
/* a much shorter proof is possible too:
	it turns out that Dafny can figure out most of the above by itself;
	all it needs is a hint (that for us is trivial, and Dafny probably didn't know it was relevant):
{
	assert q[..i+1] == q[..i]+[q[i]];
}
*/

lemma Lemma_2b(q: seq<int>, i: nat, sum: int)
	requires inv: 0 <= i <= |q| && sum == RecursiveSumDown(q[..i])
	requires neg_of_guard: i >= |q|
	ensures sum == RecursiveSumDown(q)
{
	assert i <= |q| && sum == RecursiveSumDown(q[..i]) by { reveal inv; }
	assert i == |q| by { reveal inv,neg_of_guard; }
	assert q[..i] == q[..|q|] == q;
}

// up loop: a third and final attempt, one that Dafny can prove all by itself
method ComputeSum_3(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumUp(q)
{
	var i := 0;
	sum := 0;
	while i < |q|
		invariant 0 <= i <= |q| && sum + RecursiveSumUp(q[i..]) == RecursiveSumUp(q)
		decreases |q|-i
	{
		sum := sum+q[i];
		i := i+1;
	}
}

// down loop: proving correctness on the lines of the proof to ComputeSum_1 is left as an exercise
method {:verify false} ComputeSum_4(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumDown(q)
{
	var i := |q|;
	sum := 0;
	while i > 0
		invariant 0 <= i <= |q| && sum == RecursiveSumDown(q[i..])
		decreases i
	{
		i := i-1;
		sum := sum+q[i];
	}
}

// down loop with the opposite definition in the postcondition and in the loop invariant: simpler to prove;
// proving correctness on the lines of the proof to ComputeSum_2 is left as an exercise
method {:verify false} ComputeSum_5(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumUp(q)
{
	var i := |q|;
	sum := 0;
	while i > 0
		invariant 0 <= i <= |q| && sum == RecursiveSumDown(q[i..])
		decreases i
	{
		i := i-1;
		sum := sum+q[i];
	}
}

// down loop with an invariant on the lines of the program in ComputeSum_6;
// this time Dafny is not convinced all by itself of the correctness;
// proof is left as an exerceise
method {:verify false} ComputeSum_6(q: seq<int>) returns (sum: int)
	ensures sum == RecursiveSumDown(q)
{
	var i := |q|;
	sum := 0;
	while i > 0
		invariant 0 <= i <= |q| && RecursiveSumDown(q[..i]) + sum == RecursiveSumDown(q)
		decreases i
	{
		i := i-1;
		sum := q[i]+sum;
	}
}

// one more example of proof by induction
lemma {:induction false} EquivalentSumDefinitions(q: seq<int>)
	ensures RecursiveSumDown(q) == RecursiveSumUp(q)
	decreases |q|
{
	if |q| == 0
	{
		assert q == [];
		assert RecursiveSumDown([]) == 0 == RecursiveSumUp([]);
	}
	else if |q| == 1
	{
		assert q == [q[0]];
		assert RecursiveSumDown(q) == q[0] == RecursiveSumUp(q);
	}
	else
	{
		assert |q| >= 2;
		var first, mid, last := q[0], q[1..|q|-1], q[|q|-1];
		assert q == [first] + mid + [last];
		calc {
			RecursiveSumDown(q);
		== { assert q != [] && q[|q|-1] == last && q[..|q|-1] == [first] + mid; }
			last + RecursiveSumDown([first] + mid);
		== // arithmetic
			RecursiveSumDown([first] + mid) + last;
		== { EquivalentSumDefinitions([first] + mid); } // induction hypothesis
			RecursiveSumUp([first] + mid) + last;
		== { assert [first] + mid != []; }
			first + RecursiveSumUp(mid) + last;
		== { EquivalentSumDefinitions(mid); } // induction hypothesis
			first + RecursiveSumDown(mid) + last;
		==
			first + RecursiveSumDown(mid + [last]);
		== { EquivalentSumDefinitions(mid + [last]); } // induction hypothesis
			first + RecursiveSumUp(mid + [last]);
		== { assert q != [] && q[0] == first && q[1..] == mid + [last]; }
			RecursiveSumUp(q);
		}
	}
}
