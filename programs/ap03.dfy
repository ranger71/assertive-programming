/*
Lecture #3: algorithm derivation + ghost methods for documenting (+ proving correctness of) the proof obligations

This time we aim to re-implement the Sqrt method (from the first two lectures) in logarithmic time.
Knowing how to detect the proof obligations, we derive an important portion of the code such the implementation becomes "correct by construction"!
*/

method Main() {
	var x := Sqrt(9);
	assert x == 3;
	print "The floor of the non-negative square root of 9 is ", x, "\n";
	x := Sqrt(10);
	assert x == 3;
	print "The floor of the non-negative square root of 10 is ", x, "\n";
}

// a function that returns a boolean value is commonly used, and has a keyword: predicate;
// like the local variable "V0" (used for proving termination), whenever a function or predicate is used only in specification context, we declare it as "ghost";
// this is new since Dafny 4.0; prior to that, every function/predicate was considered ghost by default, and whenever we wanted to use it in executable code,
// we needed to tell the compiler not to drop it, by declaring it with the combination of keywords "function method" or "predicate method" - which was removed in Dafny 4.0
ghost predicate Inv(n: int, lo: int, hi: int) {
	0 <= lo <= hi && // this was added after the lecture (instead of explicitly declaring "lo" and "hi" to be of type "nat")
	lo*lo <= n < hi*hi
}

// at the end of development we always like to make another copy of the method with the executable code only,
// without the assertions; it helps us get a sense for the actual code at a quick glance;
// if leaving the loop invariant (plus possibly some small part of the annotation in more complicated programs)
// in that version makes it verifiable, we keep it; otherwise, we can annotate that method with {:verify false}
// as it was verified in its original version; and keep in mind that in this course we use {:verify false} only for lemmas,
// when unable to prove them, never on methods!
// so the only unverified methods we may find in our course will be such "copies" of methods whose verification is done on their original verision
method Sqrt'(n: int) returns (res: int)
	requires n >= 0
	ensures res*res <= n < (res+1)*(res+1)
{
	var lo, hi := 0, n+1;
	while hi != lo+1
		invariant Inv(n, lo, hi)
	{
		var mid := (hi+lo)/2;
		if mid*mid <= n {
			lo := mid;
		} else {
			hi := mid;
		}
	}
	res := lo;
}

method Sqrt(n: int) returns (res: int)
	requires n >= 0
	ensures res*res <= n < (res+1)*(res+1)
{
	assert n >= 0;
	CorrectInit(n); // ==>
	assert Inv(n, 0, n+1);
	var lo, hi := 0, n+1;
	// stating the type "nat" explicitly would have helped Dafny,
	// otherwise it infers "int", and this is why I've strengthen the invariant (after the lecture) with the "0 <= lo <= hi"
	assert Inv(n, lo, hi);
	while hi != lo+1
		invariant Inv(n, lo, hi) // 0 <= lo <= hi && lo*lo <= n < hi*hi
		decreases hi-lo
	{
		assert Inv(n, lo, hi) && hi != lo+1;
		ghost var V0 := hi-lo;
		assert Inv(n, lo, hi) && hi != lo+1 && V0 == hi-lo; // propagated from above + initial V0 value
		var mid := (hi+lo)/2;
		assert Inv(n, lo, hi) && hi != lo+1 && V0 == hi-lo && mid == (hi+lo)/2; // propagated from above + initial mid value
		if mid*mid <= n { // mid*mid < n ? <= n ? at first we were not sure, and then the proof obligations convinced us to go with <=
			assert Inv(n, lo, hi) && hi != lo+1 && V0 == hi-lo && mid == (hi+lo)/2; // propagated from above the "if"
			assert mid*mid <= n; // guard of the enclosing "if"
			CorrectUpdateLo(n, lo, mid, hi, V0); // ==> [seeing that the mid*mid <= n was needed, we included it in the guard of the enclosing "if" statement]
			assert Inv(n, mid, hi) && 0 <= hi-mid < V0; // propagated from below by substituting the "hi" by "mid"
			// by the definition of Inv, the above is: 0 <= mid <= hi && mid*mid <= n < hi*hi && 0 <= hi-mid < V0
			lo := mid;
			assert Inv(n, lo, hi) && 0 <= hi-lo < V0; // propagated from below the "if" statement
		} else {
			assert Inv(n, lo, hi) && hi != lo+1 && V0 == hi-lo && mid == (hi+lo)/2; // propagated from above the "if"
			assert mid*mid > n; // negation of the guard of the enclosing "if"
			CorrectUpdateHi(n, lo, mid, hi, V0); // ==>
			assert Inv(n, lo, mid) && 0 <= mid-lo < V0; // propagated from below by substituting the "hi" by "mid"
			hi := mid;
			assert Inv(n, lo, hi) && 0 <= hi-lo < V0; // propagated from below the "if" statement
		}
		assert Inv(n, lo, hi); // the loop body must "maintain" its invariant
		assert 0 <= hi-lo < V0; // each loop iteration must bring us closer to termination
	}
	assert Inv(n, lo, hi);
	assert hi == lo+1; // negation of the loop guard
	PostconditionHolds(n, lo, hi); // ==>
	assert lo*lo <= n < (lo+1)*(lo+1); // the postcondition with "res" substituted by "lo"
	res := lo;
	assert res*res <= n < (res+1)*(res+1); // the postcondition
}

// in our course we use ghost methods in Dafny to document proof obligations;
// a keyword for "ghost method" in Dafny is "lemma"
lemma PostconditionHolds(n: int, lo: int, hi: int)
	requires Inv(n, lo, hi)
	requires hi == lo+1
	ensures lo*lo <= n < (lo+1)*(lo+1)
{} // here the lemma's body act as a request from Dafny to prove correctness; and when Dafny is not convinced, we can write the proof ourselves

// added after the lecture...
lemma CorrectInit(n: int)
	requires n >= 0
	ensures Inv(n, 0, n+1)
{}

lemma CorrectUpdateLo(n: int, lo: int, mid: int, hi: int, V0: int)
	requires Inv(n, lo, hi)
	requires hi != lo+1;
	requires V0 == hi-lo
	requires	mid == (hi+lo)/2
	requires mid*mid <= n
	ensures Inv(n, mid, hi)
	ensures 0 <= hi-mid < V0
{}

lemma CorrectUpdateHi(n: int, lo: int, mid: int, hi: int, V0: int)
	requires Inv(n, lo, hi)
	requires hi != lo+1;
	requires V0 == hi-lo
	requires	mid == (hi+lo)/2
	requires mid*mid > n
	ensures Inv(n, lo, mid)
	ensures 0 <= hi-mid < V0
{}
