// R. Ettinger, January 2022, following Carroll Morgan's development in "Programming from Specifications", in Dafny v3.3.0
// [June 2023 update for Dafny 4.1.0: turned all cases of "function/predicate method" into regular functions/predicates,
//  as the default meaning since Dafny 4 has changed; accordingly, all previously "regular" functions/predicates
//  should probably be changed to the new "ghost function/predicate", but I left them this way, compilable,
//  as their compilability did not cause here any verification problems.]
method {:verify false} HeapSort'(a: array<int>)
	ensures Sorted(a) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	var i := a.Length/2;
	while i != 0
	{
		i := i-1;
		Heapify'(a, i, a.Length);
	}
	if a.Length > 1
	{
		var i: nat := a.Length;
		while i >= 2
		{
			i := i-1;
			a[0], a[i] := a[i], a[0];
			Heapify'(a, 0, i);
		}
	}
}

method {:verify false} Heapify'(a: array<int>, l: nat, h: nat)
	requires l < h <= a.Length && ph(a[..], IndexSet(l+1, h)) && fn(a[..], h)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	var j := l;
	var left, right := LeftChild(j), RightChild(j);
	while (left < h && a[left] > a[j]) || (right < h && a[right] > a[j])
	{
		var k := if right < h && a[left] < a[right] then right else left;
		a[j], a[k] := a[k], a[j];
		j, left, right := k, LeftChild(k), RightChild(k);
	}
}

predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

function LeftChild(i: nat): nat { 2*i+1 }

function RightChild(i: nat): nat { 2*i+2 }

function Parent(i: nat): nat requires !RootIndex(i) { (i-1)/2 }

predicate RootIndex(i: nat) { i == 0 }

predicate AncestorIndex(i: nat, j: nat) decreases j-i 
{
	i == j || (j > 2*i && AncestorIndex(i, Parent(j)))
}

// for a reason unknown to me, using a predicate such as this in set comprehension expressions
// helps to avoid Dafny's "No terms found to trigger on" warning
predicate InRange(start: nat, i: nat, end: nat) { start <= i < end }

function IndexSet(start: nat, end: nat): set<nat> { set i: nat | i < end && InRange(start, i, end) }

// definition of a heap
predicate hp(q: seq<int>)
{
	ph(q, IndexSet(0, |q|))
}

predicate hp_except_at(q: seq<int>, k: nat)
{
	ph(q, IndexSet(0, |q|) - {k})
}

// partial heap
predicate ph(q: seq<int>, indices: set<nat>)
	requires forall i :: i in indices ==> i < |q|
{
	forall i,j :: i in indices && j in indices && AncestorIndex(i, j) ==> q[i] >= q[j]
}

// element j is a valid heap element (in the given range) with respect to its ancestors (lower indices)
predicate lo(q: seq<int>, l: nat, h: nat, j: nat)
	requires l <= h <= |q| && j < |q|
{
	forall i :: l <= i < h && AncestorIndex(i, j) ==> q[i] >= q[j]
}

// element j is a valid heap element (in the given range) with respect to its descendents (higher indices)
predicate hi(q: seq<int>, l: nat, h: nat, j: nat)
	requires l <= h <= |q| && j < |q|
{
	forall k :: l <= k < h && AncestorIndex(j, k) ==> q[j] >= q[k]
}

// the suffix q[i..] holds elements in their final (sorted) positions
predicate fn(q: seq<int>, i: nat)
	requires i <= |q|
{
	SortedSequence(q[i..]) &&
	forall j,k :: 0 <= j < i <= k < |q| ==> q[j] <= q[k] 
}

method HeapSort(a: array<int>)
	ensures Sorted(a) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	ghost var A := multiset(a[..]);
	MakeHeap(a, A);
	Sort(a, A);
	assert A == old(multiset(a[..]));
}

method MakeHeap(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	ensures hp(a[..]) && multiset(a[..]) == A
	modifies a
{
	var i: nat := a.Length/2;
	// second half is trivially a partial heap as it contains leaves only
	LemmaMakeHeapPre(a, i, A);
	while i != 0
		invariant i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A
		decreases i
	{
		i := i - 1;
		LemmaHeapifyNodePre(a, i, A);
		Heapify(a, i, a.Length, A);
		LemmaHeapifyNodePost(a, i, A);
	}
	LemmaMakeHeapPost(a, i, A);
}

lemma LemmaMakeHeapPre(a: array<int>, i: nat, A: multiset<int>)
	requires i == a.Length/2 && multiset(a[..]) == A // precondition of MakeHeap + the initialization
	ensures i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A // precondition of MakeHeapLoop
{}

lemma LemmaMakeHeapPost(a: array<int>, j: nat, A: multiset<int>)
	requires 0 == j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A
	ensures	hp(a[..]) && multiset(a[..]) == A // postcondition of MakeHeap
{
	// indeed, the definition of a heap ("hp") is in terms of a partial heap ("ph") for range 0..a.Length
}

lemma LemmaHeapifyNodePre(a: array<int>, i: nat, A: multiset<int>)
	// precondition of HeapifyNode
	requires 0 < i+1 <= a.Length/2 && ph(a[..], IndexSet(i+1, a.Length)) && multiset(a[..]) == A
	// precondition of Heapify with [l, h \ i, a.Length]
	ensures i < a.Length <= a.Length && ph(a[..], IndexSet(i+1, a.Length)) && fn(a[..], a.Length) && multiset(a[..]) == A
{}

lemma LemmaHeapifyNodePost(a: array<int>, i: nat, A: multiset<int>)
	// from the precondition of HeapifyNode (availabe here since "i" is no longer in the frame)
	requires 0 < i+1 <= a.Length/2
	// postcondition of Heapify with [l, h \ i, a.Length]
	requires ph(a[..], IndexSet(i, a.Length)) && fn(a[..], a.Length) && multiset(a[..]) == A
	// postcondition of HeapifyNode with [i \ i0] first (contract frame) and then the "i0" is renamed everywhere back to "i"
	ensures i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A
	ensures i < i+1
{}

method Sort(a: array<int>, ghost A: multiset<int>)
	requires hp(a[..]) && multiset(a[..]) == A
	ensures Sorted(a) && multiset(a[..]) == A
	modifies a
{
	if a.Length > 1
	{
		var i: nat := a.Length;
		while i >= 2
			invariant Inv1(a[..], i, A)
			decreases i
		{
			i := Sort2(a, i, A);
		}
	}
	else
	{
		Sort1b(a, A); // with 0 or 1 elements, the array is already sorted
	}
}

lemma Sort1b(a: array<int>, A: multiset<int>)
	requires hp(a[..]) && multiset(a[..]) == A
	requires a.Length <= 1
	ensures Sorted(a) && multiset(a[..]) == A
{}

predicate Inv1(q: seq<int>, i: nat, A: multiset<int>)
{
	1 <= i <= |q| && hp(q[..i]) && fn(q, i) && multiset(q) == A
}

method Sort2(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires Inv1(a[..], i0, A) && i0 >= 2
	ensures Inv1(a[..], i, A) && i < i0
	modifies a
{
	i := i0;
	i := i-1;
	a[0], a[i] := a[i], a[0];
	Lemma1(a, i, A);
	HeapifyRoot(a, i, A);
}

lemma Lemma1(a: array<int>, i: nat, A: multiset<int>)
	requires 2 <= i+1 <= a.Length && Inv1(a[..][0 := a[i]][i := a[0]], i+1, A)
	ensures 1 <= i < a.Length && hp_except_at(a[..i], 0) && fn(a[..], i) && multiset(a[..]) == A
{
	var q0 := a[..][0 := a[i]][i := a[0]];
	assert SortedSequence(q0[i+1..]);
	assert SortedSequence(a[i+1..]);
	assert forall j,k :: 0 <= j < i+1 <= k < |q0| ==> q0[j] <= q0[k];
	assert hp(q0[..i+1]);
	var q1 := a[..];
	assert SortedSequence(q1[i..]) by {
		forall m,n | i <= m <= n < |q1| ensures q1[m] <= q1[n] {
			if m == i
			{
				assert q1[m] == q0[0];
			}
		}
	}
	forall j,k | 0 <= j < i <= k < |q1| ensures q1[j] <= q1[k] {
		assert q1[i] == q0[0];
		assert q1[0] == q0[i];
		if j == 0 && k == i
		{
			assert q1[j] == q0[i] <= q0[0] == q1[k] by {
				assert hp(q0[..i+1]);
				assert AncestorIndex(0, i) by { RootLemma(); }
			}
		}
		else if j == 0
		{
			assert q1[j] <= q1[k];
		}
		else if k == i
		{
			assert q1[j] == q0[j] <= q0[0] == q1[k] by {
				assert hp(q0[..i+1]);
				assert AncestorIndex(0, j) by { RootLemma(); }
			}
		}
		else
		{
			assert q1[j] == q0[j] <= q0[k] == q1[k];
		}
	}
}

method HeapifyRoot(a: array<int>, i: nat, ghost A: multiset<int>)
	requires 1 <= i < a.Length && hp_except_at(a[..i], 0) && fn(a[..], i) && multiset(a[..]) == A
	ensures Inv1(a[..], i, A)
	modifies a
{
	LemmaHeapifyRootPre(a, i, A);
	Heapify(a, 0, i, A);
	LemmaHeapifyRootPost(a, i, A);
}

lemma LemmaHeapifyRootPre(a: array<int>, i: nat, A: multiset<int>)
	requires 1 <= i < a.Length && hp_except_at(a[..i], 0) && fn(a[..], i) && multiset(a[..]) == A // pre of HeapifyRoot
	ensures 0 < i <= a.Length && ph(a[..], IndexSet(1, i)) && fn(a[..], i) && multiset(a[..]) == A // pre of Heapify with [l, h \ 0, i]
{}

lemma LemmaHeapifyRootPost(a: array<int>, i: nat, A: multiset<int>)
	requires 0 < i <= a.Length // from pre of Heapify with [l, h \ 0, i] (note that l and h are not in the frame of Heapify)
	requires ph(a[..], IndexSet(0, i)) && fn(a[..], i) && multiset(a[..]) == A // post of Heapify with [l, h \ 0, i]
	ensures Inv1(a[..], i, A) // post of HeapifyRoot
{}

// "l" is the index of the element that needs fixing, "h" is the size of the heap
method Heapify(a: array<int>, l: nat, h: nat, ghost A: multiset<int>)
	requires l < h <= a.Length && ph(a[..], IndexSet(l+1, h)) && fn(a[..], h) && multiset(a[..]) == A
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h) && multiset(a[..]) == A
	modifies a
{
	// introduce local variable + leading assignment + weaken precondition + strengthen postcondition
	var j, left, right := l, LeftChild(l), RightChild(l);
	while HeapifyGuard(a, h, j, left, right) // !hi(a[..], l, h, j)
		invariant Inv2(a[..], l, h, j, left, right, A)
		decreases h-j
	{
		EquivalentGuards(a, l, h, j, left, right, A);
		j, left, right := SwapWithLargerChild(a, l, h, j, left, right, A);
	}
	EquivalentGuards(a, l, h, j, left, right, A);
	Lemma2(a, l, h, j, left, right, A);
}

predicate Inv2(q: seq<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
{
	l <= j < h <= |q| && left == LeftChild(j) && right == RightChild(j) &&
	ph(q, IndexSet(l, h) - {j}) && lo(q, l, h, j) && fn(q, h) && multiset(q) == A
}

lemma Lemma2(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
	requires Inv2(a[..], l, h, j, left, right, A) && hi(a[..], l, h, j)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h) && multiset(a[..]) == A
{}

predicate HeapifyGuard(a: array<int>, h: nat, j: nat, left: nat, right: nat)
	requires j < h <= a.Length
	reads a
{
	(left < h && a[left] > a[j]) || (right < h && a[right] > a[j])
}

lemma EquivalentGuards(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
	requires Inv2(a[..], l, h, j, left, right, A)
	ensures !hi(a[..], l, h, j) <==> HeapifyGuard(a, h, j, left, right)
{
	if right < h // both children are in the heap
	{
		calc {
			HeapifyGuard(a, h, j, left, right);
		== // by definition
			(left < h && a[left] > a[j])	|| (right < h && a[right] > a[j]);
		== { assert left < h && right < h; }
			a[left] > a[j]	|| a[right] > a[j];
		== { Lemma3a(a, l, h, j, left, right); }
			!hi(a[..], l, h, j);
		}
	}
	else if left < h // only the left child is in the heap
	{
		calc {
			HeapifyGuard(a, h, j, left, right);
		== // by definition of HeapifyGuard
			(left < h && a[left] > a[j])	|| (right < h && a[right] > a[j]);
		== { assert left < h && !(right < h); }
			a[left] > a[j];
		== { Lemma3b(a, l, h, j); }
			!hi(a[..], l, h, j);
		}
	}
	else // a leaf
	{
		assert !HeapifyGuard(a, h, j, left, right); // left and right are outside the heap (>= h)
		assert hi(a[..], l, h, j); // vacuously true, as there are no children in scope
	}
}

lemma Lemma3a(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat)
	requires l <= j < left < right < h <= a.Length && ph(a[..], IndexSet(l, h)-{j})
	requires left == LeftChild(j) && right == RightChild(j)
	ensures !hi(a[..], l, h, j) <==> a[left] > a[j]	|| a[right] > a[j]
{
	if a[left] > a[j] || a[right] > a[j]
	{
		assert AncestorIndex(j, left) && AncestorIndex(j, right);
	}
	else
	{
		forall k | l <= k < h && AncestorIndex(j, k) ensures a[j] >= a[k] {
			if k != j
			{
				assert AncestorIndex(left, k) || AncestorIndex(right, k) by { ProperAncestor(j, k); }
			}
		}
	}
}

lemma Lemma3b(a: array<int>, l: nat, h: nat, j: nat)
	requires l <= j < h <= a.Length && ph(a[..], IndexSet(l, h)-{j})
	requires RightChild(j) == h
	ensures !hi(a[..], l, h, j) <==> a[LeftChild(j)] > a[j]
{
	assert AncestorIndex(j, LeftChild(j));
}

method SwapWithLargerChild(a: array<int>, l: nat, h: nat, j0: nat, left0: nat, right0: nat, ghost A: multiset<int>) returns (j: nat, left: nat, right: nat)
	requires Inv2(a[..], l, h, j0, left0, right0, A) && !hi(a[..], l, h, j0)
	ensures Inv2(a[..], l, h, j, left, right, A) && 0 <= h-j < h-j0
	modifies a
{
	j, left, right := j0, left0, right0;
	var k := LargerChildIndex(a, l, h, j, left, right, A);
	a[j], a[k] := a[k], a[j];
	j, left, right := k, LeftChild(k), RightChild(k);
}

method LargerChildIndex(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, ghost A: multiset<int>) returns (k: nat)
	requires Inv2(a[..], l, h, j, left, right, A) && !hi(a[..], l, h, j)
	ensures k < h && Inv2(a[..][j := a[k]][k := a[j]], l, h, k, LeftChild(k), RightChild(k), A) && 0 <= h-k < h-j
{
	assert left < h; // in range, follows from !hi
	LemmaLargerChildIndex(a, l, h, j, left, right, A);
	k := GetLargerChildIndex(a, h, j, left, right);
}

// element "j" has at least one child in the heap (whose size is "h")
function GetLargerChildIndex(a: array<int>, h: nat, j: nat, left: nat, right: nat): nat
	requires j < left < h <= a.Length && left == LeftChild(j) && right == RightChild(j)
	reads a
{
	if right < h && a[left] < a[right] then right else left
}

lemma LemmaLargerChildIndex(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
	requires Inv2(a[..], l, h, j, left, right, A) && !hi(a[..], l, h, j)
	ensures var k := GetLargerChildIndex(a, h, j, left, right);
		k < h && Inv2(a[..][j := a[k]][k := a[j]], l, h, k, LeftChild(k), RightChild(k), A) && 0 <= h-k < h-j
{
	var k := GetLargerChildIndex(a, h, j, left, right);
	var q := a[..][j := a[k]][k := a[j]];
	assert ph(q, IndexSet(l, h) - {k}) by {
		var indices := IndexSet(l, h) - {k};
		forall m,n | m in indices && n in indices && AncestorIndex(m, n) ensures q[m] >= q[n]
		{
			if m == j
			{
				assert q[m] == a[k];
				assert a[k] >= q[n] by {
					if n != j
					{
						assert AncestorIndex(left, n) || AncestorIndex(right, n) by { ProperAncestor(j, n); }
					}
				}
			}
		}
	}
}

lemma RootLemma()
	ensures forall j: nat :: AncestorIndex(0, j)
{
	forall j | j >= 0 ensures AncestorIndex(0, j) {
		RootLemmaByInduction(j);
	}
}

lemma RootLemmaByInduction(j: nat)
	ensures AncestorIndex(0, j) // 0 == j || (j > 0 && AncestorIndex(0, Parent(j)))
	decreases j
{
	if j == 0
	{
		assert AncestorIndex(0, 0); // by definition
	}
	else
	{
		assert 1: AncestorIndex(0, Parent(j)) by { RootLemmaByInduction(Parent(j)); } // induction hypothesis
		assert 2: AncestorIndex(Parent(j), j);
		assert AncestorIndex(0, j) by { reveal 1,2; } // and the transitivity of AncestorIndex
	}
}

lemma ProperAncestor(i: nat, j: nat)
	requires AncestorIndex(i, j) && i != j
	ensures AncestorIndex(LeftChild(i), j) || AncestorIndex(RightChild(i), j)
{}

method Main() {
	var a: array<int> := new int[3] [4, 8, 6];
	var q0: seq<int> := a[..];
	assert q0 == [4, 8, 6];
	HeapSort(a);
	assert multiset(a[..]) == multiset(q0);
	print "the sorted version of [4, 8, 6] is ";
	print a[..];
	assert Sorted(a);
	assert a[..] == [4, 6, 8];

	a := new int[5] [3, 8, 5, -1, 10];
	q0 := a[..];
	assert q0 == [3, 8, 5, -1, 10];
	HeapSort(a);
	assert multiset(a[..]) == multiset(q0);
	print "\nthe sorted version of [3, 8, 5, -1, 10] is ";
	print a[..];
	assert Sorted(a);
	//assert a[..] == [-1, 3, 5, 8, 10];

	assert AncestorIndex(0,0);
	assert AncestorIndex(0,1);
	assert AncestorIndex(0,2);
	assert AncestorIndex(0,3); // <0,1,3>
	assert AncestorIndex(0,4); // <0,1,4>
	assert !AncestorIndex(1,0);
	assert AncestorIndex(1,1);
	assert !AncestorIndex(1,2);
	assert AncestorIndex(1,3);
	assert AncestorIndex(1,4);
	assert !AncestorIndex(2,0);
	assert !AncestorIndex(2,1);
	assert AncestorIndex(2,2);
	assert !AncestorIndex(2,3);
	assert !AncestorIndex(2,4);
	assert AncestorIndex(2,5);
	assert AncestorIndex(2,6);
}
