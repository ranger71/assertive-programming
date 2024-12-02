/* lecture 9: more on insertion sort + proofs with the forall/ensures construct

- complete the guard equivalence formulation + proof: a tranformation to replace an inefficient guard with a more efficient one
- prove correctness of the lemma that the two inner loop invariant formulations are indeed equivalent
- prove correctness of the lemma for the swap when formulated with our alternative Inv2'

*/
method Main() {
	var a: array<int> := new int[4];
	a[0],a[1],a[2],a[3] := 3,8,5,-1;
	print "Before sorting: ";
	print a[..];
	var A := multiset(a[..]);
	InsertionSort(a, A);
	assert Sorted(a[..]);
	assert multiset(a[..]) == A;
	print "\n After sorting: ";
	print a[..];
}

ghost predicate Sorted(q: seq<int>) {
	forall i, j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

ghost predicate SortedExceptAt(q: seq<int>, k: nat)
	requires k < |q|
{
	forall i, j :: 0 <= i <= j < |q| && i != k && j != k ==> q[i] <= q[j]
}

method {:verify true} InsertionSort'(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	modifies a
	ensures Sorted(a[..])
	ensures multiset(a[..]) == A
{
	var i := 0;
	while i != a.Length
		invariant Inv1(a[..], i, A)
		decreases a.Length-i
	{
		var j: nat := i;
		while j-1 >= 0 && a[j-1] > a[j]
			invariant Inv2(a[..], i, j, A)
			decreases j
		{
			a[j-1], a[j] := a[j], a[j-1];
			j := j-1;
		}
		i := i+1;
	}
}

method {:verify true} InsertionSort(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	modifies a
	ensures Sorted(a[..])
	ensures multiset(a[..]) == A
{
	assert multiset(a[..]) == A;
	// ==>?
	assert Inv1(a[..], 0, A);
	var i := 0;
	assert Inv1(a[..], i, A);
	while i != a.Length
		invariant Inv1(a[..], i, A) //0 <= i <= a.Length //&& forall j :: 0 <= j < i ==> a[j] == j
		decreases a.Length-i
	{
		assert Inv1(a[..], i, A);
		assert i != a.Length;
		ghost var V0 := a.Length-i;
		assert V0 == a.Length-i;
		assert Inv1(a[..], i, A);
		assert i != a.Length;
		Insert(a, i, A, V0);
		assert Inv1(a[..], i+1, A);
		assert 0 <= a.Length-(i+1) < V0;
		i := i+1;
		assert Inv1(a[..], i, A);
		assert 0 <= a.Length-i < V0;
	}
	assert Inv1(a[..], i, A);
	assert i == a.Length;
	// ==>?
	assert Sorted(a[..]);
	assert multiset(a[..]) == A;
}

ghost predicate Inv1(q: seq<int>, i: nat, A: multiset<int>) {
	0 <= i <= |q| && Sorted(q[..i]) && multiset(q) == A
}

method {:verify true} Insert'(a: array<int>, i: nat, ghost A: multiset<int>, ghost V0: int)
	requires V0 == a.Length-i
	requires Inv1(a[..], i, A)
	requires i != a.Length
	modifies a
	ensures Inv1(a[..], i+1, A)
	ensures 0 <= a.Length-(i+1) < V0 // we see that this is redundant: the left conjunct follows from the Inv on i+1 anf the right is always true
{
	Insert2(a, i, A); // this can only modify the *contents* of the array, not its length
}

method {:verify true} Insert(a: array<int>, i: nat, ghost A: multiset<int>, ghost V0: int)
	requires V0 == a.Length-i
	requires Inv1(a[..], i, A)
	requires i != a.Length
	modifies a
	ensures Inv1(a[..], i+1, A)
	ensures 0 <= a.Length-(i+1) < V0 // we see that this is redundant: the left conjunct follows from the Inv on i+1 anf the right is always true
{
	// in the invocation of a method we have two things to consider:
	// (1) that the precondition holds
	assert V0 == a.Length-i && Inv1(a[..], i, A) && i != a.Length; // propagated from above, from our precondition
	// ==> ( acomplete solution whan asked to document all proof obligations will call a lemma here)
	assert Inv1(a[..], i, A) && i != a.Length; // the precondition of the called method
	Insert2(a, i, A); // this can only modify the *contents* of the array, not its length
	// (2) that our postcondition follows from the postcondition of the called method and further assertions that can be propagated from above
	assert Inv1(a[..], i+1, A); // the called method's postcondition
	assert V0 == a.Length-i; // we propagate this from above: this is needed for our postcondition
	// ==>? (again, a complete solution will call a lemma)
	assert Inv1(a[..], i+1, A) && 0 <= a.Length-(i+1) < V0;
	// note 1: when reproducing the called method's spec (pre- and postcondition), don't forget to substitute catual/formal parameters
	// -- in this case it was not needed as they were the same
	// note 2: if the called method is recursive (or mutually recursive) we have a third thing to consider: termination
}

ghost predicate Inv2(q: seq<int>, i: nat, j: nat, A: multiset<int>) {
	// following Carroll Morgan's PfS:
	// the first "i+1" elements are sorted except at "j" and "a[j]" is sorted to the right (among the first "i+1" elements)
	j <= i < |q| && SortedExceptAt(q[..i+1], j) &&
	(forall k :: j < k <= i ==> q[j] < q[k]) &&
	multiset(q[..]) == A
}

// here's an equivalent formulation of Inv2 that is not as simple (for Dafny) to prove with
ghost predicate Inv2'(q: seq<int>, i: nat, j: nat, A: multiset<int>) {
//	j <= i < |q| && SortedExceptAt(q[..i+1], j) &&
	j <= i < |q| && Sorted(q[..j]+q[j+1..i+1]) && // conjecture: this is equivalent to the above comment
	(forall k :: j < k <= i ==> q[j] < q[k]) &&
	multiset(q[..]) == A
}

lemma LemmaBeforeSwap(q: seq<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2(q, i, j, A)
	requires exists k :: 0 <= k < j && q[k] > q[j]
	ensures Inv2(q[j-1 := q[j]][j := q[j-1]], i, j-1, A)
	ensures 0 <= j-1 < j
{}

lemma LemmaBeforeSwap'(q: seq<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2'(q, i, j, A)
	requires exists k :: 0 <= k < j && q[k] > q[j]
	ensures Inv2'(q[j-1 := q[j]][j := q[j-1]], i, j-1, A)
	ensures 0 <= j-1 < j
{
	LemmaEquivalentInvariants(q, i, j, A);
}

lemma LemmaInsert2'Post(q: seq<int>, i: nat, j: nat, A: multiset<int>)
	ensures Inv2(q, i, j, A) == Inv2'(q, i, j, A)
{
	LemmaEquivalentInvariants(q, i, j, A);
}

method {:verify true} Insert2''(a: array<int>, i: nat, ghost A: multiset<int>)
	requires Inv1(a[..], i, A)
	requires i != a.Length
	modifies a
	ensures Inv1(a[..], i+1, A)
{
	// a := new int[8]; // this is not allowed, as "a" is passed by value and therefore "a.Length" cannot be modified either!
	var j: nat := i;
	while j-1 >= 0 && a[j-1] > a[j]
		invariant Inv2'(a[..], i, j, A)
		decreases j
	{
		LemmaEquivalentGuards'(a[..], i, j, A);
		LemmaBeforeSwap'(a[..], i, j, A);
		a[j-1], a[j] := a[j], a[j-1];
		j := j-1;
	}
	LemmaEquivalentGuards'(a[..], i, j, A);
	assert Inv2'(a[..], i, j, A);
	LemmaInsert2'Post(a[..], i, j, A);
	assert Inv2(a[..], i, j, A);
}

method {:verify true} Insert2'(a: array<int>, i: nat, ghost A: multiset<int>)
	requires Inv1(a[..], i, A)
	requires i != a.Length
	modifies a
	ensures Inv1(a[..], i+1, A)
{
	// a := new int[8]; // this is not allowed, as "a" is passed by value and therefore "a.Length" cannot be modified either!
	var j: nat := i;
	while j-1 >= 0 && a[j-1] > a[j]
		invariant Inv2'(a[..], i, j, A)
		decreases j
	{
		LemmaEquivalentGuards'(a[..], i, j, A);
		LemmaBeforeSwap'(a[..], i, j, A);
		a[j-1], a[j] := a[j], a[j-1];
		j := j-1;
	}
	LemmaEquivalentGuards'(a[..], i, j, A);
	assert Inv2'(a[..], i, j, A);
	LemmaInsert2'Post(a[..], i, j, A);
	assert Inv2(a[..], i, j, A);
}

method {:verify true} Insert2(a: array<int>, i: nat, ghost A: multiset<int>)
	requires Inv1(a[..], i, A)
	requires i != a.Length
	modifies a
	ensures Inv1(a[..], i+1, A)
{
	// a := new int[8]; // note that this is not allowed, as "a" is passed by value and therefore "a.Length" cannot be modified either!
	assert Inv1(a[..], i, A);
	assert i != a.Length;
	// ==>?
	assert Inv2(a[..], i, i, A);
	var j: nat := i;
	assert Inv2(a[..], i, j, A);
	while j-1 >= 0 && a[j-1] > a[j]
		invariant Inv2(a[..], i, j, A)
		decreases j
	{
		LemmaEquivalentGuards(a[..], i, j, A);
		assert Inv2(a[..], i, j, A);
		assert exists k :: 0 <= k < j && a[k] > a[j];
		LemmaBeforeSwap(a[..], i, j, A); // ==>?
		assert Inv2(a[..][j-1 := a[j]][j := a[j-1]], i, j-1, A);
		assert 0 <= j-1 < j;
		ghost var V0 := j;
		assert Inv2(a[..][j-1 := a[j]][j := a[j-1]], i, j-1, A);
		assert 0 <= j-1 < V0;
		a[j-1], a[j] := a[j], a[j-1];
		assert Inv2(a[..], i, j-1, A);
		assert 0 <= j-1 < V0;
		j := j-1;
		assert Inv2(a[..], i, j, A);
		assert 0 <= j < V0;
	}
	LemmaEquivalentGuards(a[..], i, j, A);
	assert !exists k :: 0 <= k < j && a[k] > a[j];
	assert Inv2(a[..], i, j, A);
	// ==>
	assert Inv1(a[..], i+1, A);
}

lemma LemmaEquivalentGuards(q: seq<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2(q, i, j, A)
	ensures (j-1 >= 0 && q[j-1] > q[j]) <==> (exists k :: 0 <= k < j && q[k] > q[j])
{}

lemma LemmaEquivalentGuards'(q: seq<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2'(q, i, j, A) // we could have settled for the "j < |q| && Sorted(q[..j]))"
	ensures (j-1 >= 0 && q[j-1] > q[j]) <==> (exists k :: 0 <= k < j && q[k] > q[j])
{
	assert Inv2(q, i, j, A) by {
		assert Inv2'(q, i, j, A);
		LemmaEquivalentInvariants(q, i, j, A);
	}
}

lemma {:verify true} LemmaEquivalentInvariants(q: seq<int>, i: nat, j: nat, A: multiset<int>)
	ensures Inv2(q, i, j, A) == Inv2'(q, i, j, A)
{
	calc {
		Inv2(q, i, j, A);
	== // definition of Inv2
		j <= i < |q| && SortedExceptAt(q[..i+1], j) &&
		(forall k :: j < k <= i ==> q[j] < q[k]) &&
		multiset(q[..]) == A;
	== { LemmaEquivalentDefinitionsOfSortedExpectAt(q, i, j); }
		j <= i < |q| && Sorted(q[..j]+q[j+1..i+1]) &&
		(forall k :: j < k <= i ==> q[j] < q[k]) &&
		multiset(q[..]) == A;
	== // definition of Inv2'
		Inv2'(q, i, j, A);
	}
}

lemma {:verify true} LemmaEquivalentDefinitionsOfSortedExpectAt(q: seq<int>, i: nat, j: nat)
	ensures j <= i < |q| && SortedExceptAt(q[..i+1], j) <==> j <= i < |q| && Sorted(q[..j]+q[j+1..i+1])
{
	// proved after the lecture
	if j <= i < |q| {
		var q', k, q'' := q[..i+1], j, q[..j]+q[j+1..i+1];
		if SortedExceptAt(q', j) {
			assert Sorted(q'') by {
				forall i, j | 0 <= i <= j < |q''| ensures q''[i] <= q''[j] {
					if i < k {
						assert q''[i] == q'[i];
						if j < k {
							assert q''[j] == q'[j];
						}
						else {
							assert q''[j] == q'[j+1] && j+1 != k;
						}
					}
					else {
						assert q''[i] == q'[i+1] && i+1 != k;
						assert q''[j] == q'[j+1] && j+1 != k;
					}
				}
			}
		}
		if Sorted(q'') {
			assert SortedExceptAt(q', k) by {
				forall i, j | 0 <= i <= j < |q'| && i != k && j != k ensures q'[i] <= q'[j] {
					if i < k {
						assert q'[i] == q[i] == q''[i];
						if j < k {
							assert q'[j] == q[j] == q''[j];
						}
						else {
							assert q'[j] == q[j] == q''[j-1];
						}
					}
					else {
						assert q'[i] == q[i] == q''[i-1] && q'[j] == q[j] == q''[j-1];
					}
				}
			}
		}
	}
}

//////////////////////////////////////////////////////////////////////////////
// here's the program from a previous iteration of the course,
// where the insertion inveriant was formulated using sequence concatenation,
// confusing the Dafny verifier, providing an opportunity to demonstrate
// some advanced proof techniques:
method AP_1_22_InsertionSort'(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	ensures Sorted(a[..])
	ensures multiset(a[..]) == A
	modifies a
{
	var i := 0;
	while i < a.Length
		invariant AP_1_22_PrefixIsAlreadySorted(a, i, A)
	{
		var j: nat := i;
		while j > 0 && a[j] < a[j-1]
			invariant AP_1_22_SortedExceptJandFromJ(a[..], i, j, A)
			decreases j
		{
			AP_1_22_InsertionStepIsCorrect(a[..], i, j, j, A);
			a[j-1], a[j] := a[j], a[j-1];
			j := j-1;
		}
		AP_1_22_EquivalentGuards(a, i, j, A);
		i := i+1;
	}
}

method AP_1_22_InsertionSort(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	ensures Sorted(a[..])
	ensures multiset(a[..]) == A
	modifies a
{
	var i := 0;
	while i < a.Length
		invariant AP_1_22_PrefixIsAlreadySorted(a, i, A)
	{
		assert AP_1_22_PrefixIsAlreadySorted(a, i, A) && i < a.Length;
		AP_1_22_Insert(a, i, A);
		assert AP_1_22_PrefixIsAlreadySorted(a, i+1, A);
		i := i+1;
		assert AP_1_22_PrefixIsAlreadySorted(a, i, A);
	}
}

ghost predicate AP_1_22_PrefixIsAlreadySorted(a: array<int>, i: nat, A: multiset<int>)
	reads a
{
	0 <= i <= a.Length && Sorted(a[..i]) && multiset(a[..]) == A
}

method AP_1_22_Insert(a: array<int>, i: nat, ghost A: multiset<int>)
	requires AP_1_22_PrefixIsAlreadySorted(a, i, A) && i < a.Length
	ensures  AP_1_22_PrefixIsAlreadySorted(a, i+1, A)
	modifies a
{
	var j: nat := i;
	while j > 0 && a[j] < a[j-1]
		invariant AP_1_22_SortedExceptJandFromJ(a[..], i, j, A)
		decreases j
	{
		ghost var j0 := j;
		AP_1_22_EquivalentGuards(a, i, j, A);
		assert AP_1_22_SortedExceptJandFromJ(a[..], i, j, A) && !Sorted(a[..j+1]) && j == j0;
		AP_1_22_InsertionStepIsCorrect(a[..], i, j, j0, A);
		assert AP_1_22_SortedExceptJandFromJ(a[..][j-1 := a[j]][j := a[j-1]], i, j-1, A) && j-1 < j0;
		a[j-1], a[j] := a[j], a[j-1];
		assert AP_1_22_SortedExceptJandFromJ(a[..], i, j-1, A) && j-1 < j0;
		j := j-1;
		assert AP_1_22_SortedExceptJandFromJ(a[..], i, j, A) && j < j0;
	}
	AP_1_22_EquivalentGuards(a, i, j, A);
	// added after lecture 8 (even though Dafny was convinced of the correctness)
	AP_1_22_InsertIsCorrect(a, i, j, A);
}

lemma {:verify false} AP_1_22_EquivalentGuards(a: array<int>, i: nat, j: nat, A: multiset<int>)
	requires AP_1_22_SortedExceptJandFromJ(a[..], i, j, A)
	ensures j > 0 && a[j] < a[j-1] <==> !Sorted(a[..j+1])
{}

ghost predicate AP_1_22_SortedExceptJandFromJ(q: seq<int>, i: nat, j: nat, A: multiset<int>)
{
	j <= i < |q| && Sorted(q[..j]+q[j+1..i+1]) && Sorted(q[j..i+1]) && multiset(q) == A
}

// this was added after the lecture
lemma AP_1_22_InsertIsCorrect(a: array<int>, i: nat, j: nat, A: multiset<int>)
	requires pre1: AP_1_22_SortedExceptJandFromJ(a[..], i, j, A)
	requires pre2: Sorted(a[..j+1])
	ensures AP_1_22_PrefixIsAlreadySorted(a, i+1, A)
{
	// Dafny would accept this simply with "reveal pre1,pre2;"
	// Still, let's practice writing a fully detailed proof (for the human reader)
	var q := a[..];
	assert |q| == a.Length && q == a[..];
	// first let's recall what we know from pre1:
	assert j <= i < |q|                      by { reveal pre1; }
	assert pre1a: Sorted(q[..j]+q[j+1..i+1]) by { reveal pre1; } // this portion appears not to be needed here
	assert pre1b: Sorted(q[j..i+1])          by { reveal pre1; }
	assert pre1c: multiset(q) == A           by { reveal pre1; }
	// now let's break the postcondition PrefixIsAlreadySorted(a, i+1, A) into its three parts
	assert 0 <= i+1 <= a.Length by { assert i < a.Length by { reveal pre1; } } // and the type of "i" (nat)
	assert Sorted(a[..i+1]) by {
		// the prefix including a[j] is sorted and the subsequence from a[j] to a[i] is sorted too, so the prefix up until a[i] should be sorted 
		var q1, q2, q3 := q[..i+1], q[..j+1], q[j..i+1];
		assert q1 == a[..i+1] && |q1| == i+1;
		forall i',j' | 0 <= i' <= j' < |q1| ensures q1[i'] <= q1[j'] {
			if j' <= j
			{
				// both in a[..j+1]
				assert q1[i'] <= q1[j'] by { reveal pre2; assert q1[i'] == a[i'] && q1[j'] == a[j']; }
			}
			else if j <= i'
			{
				// both in q3 (== q[j..i+1]) with an offset of "j" elements
				assert j <= i' <= j' < |q1|;
				assert q1[i'] == q3[i'-j] && q1[j'] == q3[j'-j];
				assert q1[i'] <= q1[j'] by { reveal pre1b; assert q1[i'] == q3[i'-j] && q1[j'] == q3[j'-j]; }
			}
			else
			{
				// one in q2 the other in q3, both sorted, with "q[j]" the largest in q2 and smallest in q3,
				// so from the transitivity of "<=" we should have q[i'] <= q[j] <= q[j']
				assert i' < j < j' < i+1;
				calc {
					q1[i'];
				== { assert q1[..j+1] == q2; }
					q2[i'];
				<= { reveal pre2; assert Sorted(q2); }
					q2[j];
				== { assert q2 == q1[..j+1]; }
					q1[j];
				== { assert q1[j..] == q3; }
					q3[0];
				<= { reveal pre1b; assert Sorted(q3); }
					q3[j'-j];
				== { assert q3 == q1[j..]; }
					q1[j'];
				}
			}
		}
	}
	assert multiset(a[..]) == A by { reveal pre1c; }
}

lemma {:verify true} AP_1_22_InsertionStepIsCorrect(q: seq<int>, i: nat, j: nat, j0: nat, A: multiset<int>)
	requires loop_inv: AP_1_22_SortedExceptJandFromJ(q, i, j, A)
	requires loop_guard: !Sorted(q[..j+1])
	requires variant: j == j0
	ensures AP_1_22_SortedExceptJandFromJ(q[j-1 := q[j]][j := q[j-1]], i, j-1, A) && j-1 < j0
{
	// as in the proof above, let's first write in detail all we know from the preconditions:
	assert j <= i < |q|                      by { reveal loop_inv; }
	assert inv_a: Sorted(q[..j]+q[j+1..i+1]) by { reveal loop_inv; }
	assert inv_b: Sorted(q[j..i+1])          by { reveal loop_inv; }
	assert inv_c: multiset(q) == A           by { reveal loop_inv; }
	// from the preconditions we know the swap is needed
	assert 0 < j by { reveal loop_guard; }
	var q1 := q[..j]+q[j+1..i+1];
	// q[..j] is sorted yet q[..j+1] is NOT, so q[j-1] must be larger than q[j]
	assert swap_is_needed: q[j-1] > q[j] by { reveal inv_a; AP_1_22_SortedSubsequence(q1, 0, j); assert Sorted(q[..j]); reveal loop_guard; }
	// now let's break the postcondition into its individual conjuncts and prove each:
	var q' := q[j-1 := q[j]][j := q[j-1]]; // sequence of elements after swapping
	var j' := j-1;
	assert j' <= i < |q'| by { reveal loop_inv; }
	assert Sorted(q'[..j']+q'[j'+1..i+1]) by {
		calc {
			q'[..j']+q'[j'+1..i+1];
		==
			q[..j-1]+q'[j..i+1];
		== // def. of q'
			q[..j-1]+q[j-1 := q[j]][j := q[j-1]][j..i+1];
		== // ignore the out-of-scope sequence assignment (at j-1)
			q[..j-1]+q[j := q[j-1]][j..i+1];
		==
			q[..j-1]+[q[j-1]]+q[j+1..i+1];
		==
			q[..j]+q[j+1..i+1];
		== // def. of q1
			q1;
		 }
		 assert Sorted(q1) by { reveal inv_a; }
	}
	assert Sorted(q'[j'..i+1]) by {
		var q2' := [q[j],q[j-1]]+q[j+1..i+1];
		assert q'[j'..i+1] == q2';
		assert Sorted(q2') by {
			forall m,n | 0 <= m <= n < |q2'| ensures q2'[m] <= q2'[n] {
				if m == 0
				{
					if n == 1
					{
						assert q2'[m] <= q2'[n] by { reveal swap_is_needed; }
					}
					else if 1 < n
					{
						assert q2'[m] <= q2'[n] by { reveal inv_b; }
					}
				}
				else if m == 1
				{
					if m < n
					{
						var q3 := q[..j]+q[j+1..i+1];
						assert q2'[m] == q'[1+j'] == q'[j] == q[j-1] == q3[j-1] <= q3[n+j-2] == q[n+j-1] == q'[n+j'] == q2'[n] by { reveal inv_a; }
					}
				}
				else
				{
					assert 2 <= m <= n;
					var q3 := q[..j]+q[j+1..i+1];
					assert q2'[m] == q'[m+j'] == q[m+j-1] == q3[m+j-2] <= q3[n+j-2] == q[n+j-1] == q'[n+j'] == q2'[n] by { reveal inv_a; }
				}
			}
		}
	}
	assert multiset(q') == A by {
		calc {
			multiset(q');
		== // def. of q'
			multiset(q[j-1 := q[j]][j := q[j-1]]);
		== { AP_1_22_SwapMaintainsMultiset(q, j-1, j); }
			multiset(q);
		== { reveal inv_c; }
			A;
		}
	}
	assert j-1 < j0 by { reveal variant; }
}

lemma AP_1_22_SortedSubsequence(q: seq<int>, i: nat, j: nat)
	requires Sorted(q) && i <= j <= |q|
	ensures Sorted(q[i..j])
{}

lemma AP_1_22_SwapMaintainsMultiset(q: seq<int>, i: nat, j: nat)
	requires i < j < |q|
	ensures multiset(q[i := q[j]][j := q[i]]) == multiset(q)
{}

// the correctness of this version (same outer loop invariant, different inner loop invariant)
// is verified by Dafny automatically, with no need for manual proof
method AP_1_22_InsertionSort2(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	ensures Sorted(a[..])
	ensures multiset(a[..]) == A
	modifies a
{
	var i := 0;
	while i < a.Length
		invariant i <= a.Length && Sorted(a[..i]) && multiset(a[..]) == A
	{
		var j: nat := i;
		while j > 0 && a[j-1] > a[j]
			invariant j <= i < a.Length && multiset(a[..]) == A
			invariant forall m,n :: 0 <= m <= n <= i && m != j && n != j ==> a[m] <= a[n] // a[..i+1] is sorted except at j
			invariant forall k :: j < k <= i ==> a[j] < a[k] // a[j] is sorted too, to  its right, within a[..i+1] (elements of a[j+1..i+1]) 
			decreases j
		{
			a[j-1], a[j] := a[j], a[j-1];
			j := j-1;
		}
		// on exit from the inner loop, beyond the invariant,
		// guaranteeing that a[..i+1] is sorted except at j and a[j] is sorted to its right (elements of a[j+1..i+1]),
		// a[j] is sorted to its left too (elements of a[..j])
		i := i+1;
	}
}
