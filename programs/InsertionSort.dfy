method Main() {
	var a: array<int> := new int[4] [3,8,5,-1];
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

method InsertionSort'(a: array<int>, ghost A: multiset<int>)
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

method InsertionSort(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	modifies a
	ensures Sorted(a[..])
	ensures multiset(a[..]) == A
{
	assert multiset(a[..]) == A;
	// ==>
	assert Inv1(a[..], 0, A);
	var i := 0;
	assert Inv1(a[..], i, A);
	while i != a.Length
		invariant Inv1(a[..], i, A)
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
	// ==>
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
	ensures 0 <= a.Length-(i+1) < V0
{
	Insert2(a, i, A);
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

lemma LemmaBeforeSwap(q: seq<int>, i: nat, j: nat, A: multiset<int>)
	requires Inv2(q, i, j, A)
	requires exists k :: 0 <= k < j && q[k] > q[j]
	ensures Inv2(q[j-1 := q[j]][j := q[j-1]], i, j-1, A)
	ensures 0 <= j-1 < j
{}

method {:verify true} Insert2(a: array<int>, i: nat, ghost A: multiset<int>)
	requires Inv1(a[..], i, A)
	requires i != a.Length
	modifies a
	ensures Inv1(a[..], i+1, A)
{
	assert Inv1(a[..], i, A);
	assert i != a.Length;
	// ==>
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
		LemmaBeforeSwap(a[..], i, j, A);
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