method Main() {
	var a: array<int> := new int[4] [3,8,5,-1];
	print "Before sorting: ";
	print a[..];
	ghost var A := multiset(a[..]);
	NoSoStupidSort(a, A);
	assert Sorted(a[..]);
	assert multiset(a[..]) == A;
	print "\n After sorting: ";
	print a[..];
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

predicate Inv(q: seq<int>, i: nat, A: multiset<int>)
{
	i <= |q| && Sorted(q[..i]) && multiset(q) == A
}

predicate Inv2(q: seq<int>, i: nat, j: nat, A: multiset<int>)
{
	0 <= i < |q| && 0 <= j <= |q| && (j < i ==> forall k | 0 <= k < j :: q[k] <= q[i]) && 
				(j >= i ==> Sorted(q[..i+1])) && (j < i ==> Sorted(q[..i])) && multiset(q[..]) == A
}

lemma Lemma0 (a: seq<int>, A: multiset<int>)
	requires multiset(a[..]) == A
	ensures Inv(a[..],0,A)
{}

lemma Lemma1 (a: seq<int>, i: nat, A: multiset<int>, V0: int)
	requires V0 == |a|-i
	requires Inv(a,i,A)
	requires i != |a|
	ensures Inv2(a[..],i,0,A)
	ensures V0 == |a|-i
{}

lemma Lemma2 (a: seq<int>, i: nat, j: nat, A: multiset<int>, V1: int)
	requires j != |a|
	requires Inv2(a,i,j,A)
	requires (a[i] < a[j])
	requires V1 == |a|-j
	ensures Inv2(a[..][i := a[j]][j := a[i]],i,j+1,A)
	ensures 0 <= |a|-(j+1) < V1
{}

lemma Lemma3 (a: seq<int>, i: nat, j: nat, A: multiset<int>, V1: int)
	requires j != |a|
	requires Inv2(a[..],i,j,A)
	requires a[i] >= a[j]
	requires V1 == |a|-j
	ensures Inv2(a[..],i,j+1,A)
	ensures 0 <= |a|-(j+1) < V1
{}

lemma Lemma4 (a: seq<int>, i: nat, j: nat, A: multiset<int>, V0: int)
	requires j == |a|
	requires Inv2(a[..],i,j,A)
	requires V0 == |a|-i
	ensures Inv(a[..],i+1,A)
	ensures 0 <= |a|-(i+1) < V0
{}

lemma Lemma5 (a: seq<int>, i: nat, A: multiset<int>)
	requires Inv(a,i,A) && i == |a|
	ensures Sorted(a) && multiset(a) == A
{}

// TODO: prove correctness of the following sorting algorithm, documenting the proof obligations,
// eventually replacing the "{:verify false}" with "{:verify true}";
// feel free to consult with the corresponding proof in Ada/SPARK (as briefly seen in class too):
// https://blog.adacore.com/i-cant-believe-that-i-can-prove-that-it-can-sort
method {:verify true} NoSoStupidSort(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	ensures Sorted(a[..])
	ensures multiset(a[..]) == A
	modifies a
{
	assert multiset(a[..]) == A;
	Lemma0(a[..], A);
	assert Inv(a[..],0,A);
	var i := 0;
	assert Inv(a[..],i,A);
	while (i != a.Length)
    invariant Inv(a[..],i,A)
    decreases a.Length-i
	{
		ghost var V0 := a.Length-i;
		assert V0 == a.Length-i;
		assert Inv(a[..],i,A);
		assert i != a.Length;
		Lemma1(a[..], i, A, V0);
		assert Inv2(a[..],i,0,A);
		assert V0 == a.Length-i;
		var j := 0;
		assert Inv2(a[..],i,j,A);
		assert V0 == a.Length-i;
		while (j != a.Length)
			invariant Inv2(a[..],i,j,A)
			decreases a.Length-j
		{
			assert Inv2(a[..],i,j,A);
			assert j != a.Length;
			ghost var V1 := a.Length-j;
			assert V1 == a.Length-j;
			if (a[i] < a[j])
			{
				assert a[i] < a[j]; // if condition
				assert Inv2(a[..],i,j,A);
				assert j != a.Length;
				assert V1 == a.Length-j;
				Lemma2(a[..], i, j, A, V1);
				assert Inv2(a[..][i := a[j]][j := a[i]],i,j+1,A);
				assert 0 <= a.Length-(j+1) < V1;
				a[i], a[j] := a[j], a[i]; // swap
				assert Inv2(a[..],i,j+1,A);
				assert 0 <= a.Length-(j+1) < V1;
			}
			else
			{
				assert a[i] >= a[j];
				assert Inv2(a[..],i,j,A);
				assert j != a.Length;
				assert V1 == a.Length-j;
				Lemma3(a[..], i, j, A, V1);
				assert Inv2(a[..],i,j+1,A);
				assert 0 <= a.Length-(j+1) < V1;
			}
			assert Inv2(a[..],i,j+1,A);
			assert V1 == a.Length-j;
			assert 0 <= a.Length-(j+1) < V1;
			j := j+1;
			assert Inv2(a[..],i,j,A);
			assert 0 <= a.Length-j < V1;
		}
		assert Inv2(a[..],i,j,A); // maintaining the second loop invariant
		assert j == a.Length; // the second loop termination
		assert V0 == a.Length-i;
		Lemma4(a[..], i, j, A, V0);
		assert Inv(a[..],i+1,A);
		assert 0 <= a.Length-(i+1) < V0;
		i := i+1;
		assert Inv(a[..],i,A);
		assert 0 <= a.Length-i < V0;
	}
	assert Inv(a[..],i,A);  // maintaining the first loop invariant
	assert i == a.Length; // the first loop termination
	Lemma5(a[..],i,A);
	assert Sorted(a[..]) && multiset(a[..]) == A;
}