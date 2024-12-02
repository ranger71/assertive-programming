/*
Lecture #2: Verification Conditions / Proof Obligations
*/
method Sqrt(n: int) returns (res: int)
	requires n >= 0
	ensures res*res <= n < (res+1)*(res+1)
{
	res := 0;
	while !(n < (res+1)*(res+1))
		invariant res*res <= n
		decreases n - res*res
	{
		res := res+1;
	}
}

method Sqrt_annotated_without_termination(n: int) returns (res: int)
	requires n >= 0
	ensures res*res <= n < (res+1)*(res+1)
{
	assert n >= 0; // the precondition
	// ==>?
	assert 0*0 <= n; // propagated from below by "substitution" of the assignment's LHS by its RHS
	res := 0;
	assert res*res <= n; // the base case for the loop invariant
	while !(n < (res+1)*(res+1))
		invariant res*res <= n
		decreases n - res*res // in this version we let Dafny verify termination with ths hint alone; see a version below with all proof obligation documented (for termination too)
	{
		assert !(n < (res+1)*(res+1)); // the loop guard (otherwise we would not reach this point)
		assert res*res <= n; // the loop invariant: we assume it holds here, just like an induction hypothesis
		// ==>? (actually this time, the loop guard was strong enough, in later cases, we'd probably need to assume the loop invariant holds above too)
		assert (res+1)*(res+1) <= n; // propagated from below by "substitution" of the assignment's LHS by its RHS
		res := res+1;
		assert res*res <= n; // the induction step for the loop invariant
	}
	assert n < (res+1)*(res+1); // negation of the loop guard
	assert res*res <= n; // the loop invariant
	// ==>?
	assert res*res <= n < (res+1)*(res+1); // the postcondition
}

method Sqrt_with_termination(n: int) returns (res: int)
	requires n >= 0
	ensures res*res <= n < (res+1)*(res+1)
{
	assert n >= 0; // the precondition
	// ==>?
	assert 0*0 <= n; // propagated from below by "substitution" of the assignment's LHS by its RHS
	res := 0;
	assert res*res <= n; // the base case for the loop invariant
	while !(n < (res+1)*(res+1))
		invariant res*res <= n
		decreases n - res*res // the loop variant: an integer-valued expression whose value must decrease at each iteration yet never below some lower bound (typically 0)
	{
		assert !(n < (res+1)*(res+1)); // the loop guard (otherwise we would not reach this point)
		assert res*res <= n; // the loop invariant: we assume it holds here, just like an induction hypothesis
		// ==>?
		// propagated from below by "substitution" of the assignment's LHS by its RHS
		assert (res+1)*(res+1) <= n;
		assert 0 <= n - (res+1)*(res+1) < n - res*res;

		ghost var V0 := n - res*res; // backup of the variant expression at the head of an iteration
		// propagated from below by "substitution" of the assignment's LHS by its RHS
		assert (res+1)*(res+1) <= n;
		assert 0 <= n - (res+1)*(res+1) < V0;
		res := res+1;
		assert res*res <= n; // the induction step for the loop invariant
		assert 0 <= n - res*res < V0; // guarantee progress towards termination
	}
	assert n < (res+1)*(res+1); // negation of the loop guard
	assert res*res <= n; // the loop invariant
	// ==>?
	assert res*res <= n < (res+1)*(res+1); // the postcondition
}

method Main() {
	//var x := Sqrt(-9); // a precondition might not hold!
	var x := Sqrt(9);
	assert x*x <= 9 < (x+1)*(x+1); // from the postcondition
	// ==>
	assert x == 3;
	print "The floor of the non-negative square root of 9 is ", x, "\n";
	x := Sqrt(10);
	assert x == 3;
	print "The floor of the non-negative square root of 10 is ", x, "\n";
}