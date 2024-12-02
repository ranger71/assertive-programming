// InsertionSort session #1: the spec + the outer loop + derive a spec for the Insert operation
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
	forall i :: 0 <= i && i+1 < |q| ==> q[i] <= q[i+1] // we may want to update this later to a quantifier on two indices
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
		ghost var V0 := a.Length-i;
		Insert(a, i, A, V0);
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

method {:verify false} Insert(a: array<int>, i: nat, ghost A: multiset<int>, ghost V0: int)
	requires V0 == a.Length-i
	requires Inv1(a[..], i, A)
	requires i != a.Length
	modifies a
	ensures Inv1(a[..], i+1, A)
	ensures 0 <= a.Length-(i+1) < V0
{
	// TODO: verify correctness (next week) - or fix, if there's a bug
	var j := i;
	while exists k :: 0 <= k < j && a[k] > a[j] // TODO: replace this loop guard with a more "efficient" one
		invariant 0 <= j <= i < a.Length // TODO: strengthen the invariant (next week)
		decreases j
	{
		a[j-1], a[j] := a[j], a[j-1];
		j := j-1;
	}
}
