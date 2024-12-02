// at the bottom I've added after the lecture two interesting solutions from previous years,
// one with an early return inside the loop body, the other with a simple loop,
// updating the boolean "found" only after exiting the loop (+ a detailed proof of a lemma)
method Main() {
	var a: array<int> := new int[4];
	a[0], a[1], a[2], a[3] := 9, 7, 8, 7;
	var found, i := SearchArray(a, 7);
	assert found;
	assert i == 1 || i == 3;
	print "[9,7,8,7][";
	print i;
	print "] = 7\n";

	var a2: array<int> := new int[1];
	a2[0] := 4;
	found, i := SearchArray(a2, 4);
	assert found;
	assert i == 0;
	print "[4][";
	print i;
	print "] = 4\n";

	found, i := SearchArray(a2, 14);
	assert !found;
}

ghost predicate Inv(a: array<int>, key: int, i: nat, found: bool)
	reads a
{
	i < a.Length &&
	(key in a[..i+1]  <==> found) &&
	(found ==> (i < a.Length && a[i] == key))
}

method SearchArray'(a: array<int>, key: int) returns (found: bool, i: nat)
	ensures key in a[..]  <==> found
	ensures found ==> i < a.Length && a[i] == key
{
	if a.Length == 0 {
		found, i := false, 0;
	}
	else {
		found, i := a[0] == key, 0;
		while !found && i+1 < a.Length
			invariant Inv(a, key, i, found)
			decreases a.Length-i, if !found then 1 else 0
		{
			if i+1 < a.Length && a[i+1] == key {
				found := true;
			}
			i := i+1;
		}
	}
}

method {:verify true} SearchArray(a: array<int>, key: int) returns (found: bool, i: nat)
	ensures key in a[..]  <==> found
	ensures found ==> i < a.Length && a[i] == key
{
	if a.Length == 0 {
		assert a.Length == 0;
		// ==>?
		assert key in a[..]  <==> false;
		assert false ==> i < a.Length && a[i] == key;
		found, i := false, 0; // the value of "i" does not really matter here
		assert key in a[..]  <==> found;
		assert found ==> i < a.Length && a[i] == key;
	}
	else {
		found, i := a[0] == key, 0;
		while !found && i+1 < a.Length
			invariant Inv(a, key, i, found)
			decreases a.Length-i, if !found then 1 else 0
		{
			assert Inv(a, key, i, found);
			assert !found && i+1 < a.Length;
			if i+1 < a.Length && a[i+1] == key
			{
				assert Inv(a, key, i, found);
				assert !found && i < a.Length;
				assert i+1 < a.Length && a[i+1] == key;
				// ==>?
				assert Inv(a, key, i+1, true);
				found := true;
				assert Inv(a, key, i+1, found);
			}
			else {
				assert Inv(a, key, i, found);
				assert !found && i < a.Length;
				assert !(i+1 < a.Length && a[i+1] == key);
				// ==>?
				assert Inv(a, key, i+1, found);
			}
			i := i+1;
			assert Inv(a, key, i, found);
		}
		assert Inv(a, key, i, found);
		assert found || i+1 >= a.Length;
		// ==>?
		assert key in a[..]  <==> found;
		assert found ==> i < a.Length && a[i] == key;
	}
	assert key in a[..]  <==> found;
	assert found ==> i < a.Length && a[i] == key;
}

// two further solutions, from a previous iteration of this course:
method {:verify true} SearchArray2_with_early_return'(a: array<int>, key: int) returns (found: bool, i: nat)
	ensures key in a[..] <==> found
	ensures found ==> i < a.Length && a[i] == key
{
	i := 0;
	while i < a.Length
		invariant i <= a.Length && key !in a[..i]
	{
		if a[i] == key
		{
			found := true;
			return;
		}
		i := i+1;
	}
	found := false;
}

method {:verify true} SearchArray2_with_early_return(a: array<int>, key: int) returns (found: bool, i: nat)
	ensures key in a[..] <==> found
	ensures found ==> i < a.Length && a[i] == key
{
	i := 0;
	while i < a.Length
		invariant i <= a.Length && key !in a[..i]
	{
		if a[i] == key
		{
			assert key in a[..] <==> true by { assert a[i] == key; }
			assert true ==> i < a.Length && a[i] == key; // from the guards above (loop and if)
			found := true;
			assert key in a[..] <==> found;
			assert found ==> i < a.Length && a[i] == key;
			return;
		}
		i := i+1;
	}
	assert i <= a.Length && key !in a[..i]; // inv
	assert !(i < a.Length); // negation of the loop guard
	// ==> (from the above, we get "key !in a[..a.Length]", meaning "key !in a[..]")
	assert key in a[..] <==> false; // == key !in a[..]
	assert false ==> i < a.Length && a[i] == key; // == true
	found := false;
	assert key in a[..] <==> found;
	assert found ==> i < a.Length && a[i] == key;
}

// a version with the simplest loop body: 
method {:verify true} SearchArray3'(a: array<int>, key: int) returns (found: bool, i: nat)
	ensures key in a[..] <==> found
	ensures found ==> i < a.Length && a[i] == key
{
	i := 0;
	while i < a.Length && a[i] != key
		invariant i <= a.Length && key !in a[..i]
		decreases a.Length-i
	{
		i := i+1;
	}
	L3(a, key, i);
	found := i < a.Length;
}

method {:verify true} SearchArray3(a: array<int>, key: int) returns (found: bool, i: nat)
	ensures key in a[..] <==> found
	ensures found ==> i < a.Length && a[i] == key
{
	// init (establish the invariant)
	i := 0;
	assert i <= a.Length && key !in a[..i];
	while i < a.Length && a[i] != key
		invariant i <= a.Length && key !in a[..i]
		decreases a.Length-i
	{
		i := i+1;
	}
	// inv && !guard
	assert i <= a.Length && key !in a[..i];
	assert !(i < a.Length && a[i] != key); // so i is a.Length or a[i] is the key
	// the method's postcondition with substitution ("i < a.Length" for "found"); is it implied by (inv and !guard)?
	L3(a, key, i);
	assert key in a[..] <==> i < a.Length;
	assert i < a.Length ==> i < a.Length && a[i] == key;
	found := i < a.Length;
	assert key in a[..] <==> found;
	assert found ==> i < a.Length && a[i] == key;
}

lemma L3(a: array<int>, key: int, i: nat)
	requires pre1: i <= a.Length
	requires pre2: key !in a[..i]
	requires pre3: !(i < a.Length && a[i] != key)
	ensures key in a[..] <==> i < a.Length               // post1
	ensures i < a.Length ==> i < a.Length && a[i] == key // post2
{
	// let's start with post2 (and one side of post1 will follow from that)
	assert from_pre3: i >= a.Length || a[i] == key by { reveal pre3; } // De Morgan
	if i < a.Length
	{
		assert i < a.Length && a[i] == key by { reveal from_pre3; }
	}
	// post1 (==>)
	if key in a[..]
	{
		assert somewhere_in_the_array: exists j :: 0 <= j < a.Length && a[j] == key; // by the guard above
		assert i <= a.Length by { reveal pre1; } // without that we're not allowed to refer to a prefix of length "i"
		assert not_in_prefix: key !in a[..i] by { reveal pre2; }
		assert suffix_not_empty: exists j :: i <= j < a.Length && a[j] == key by { reveal not_in_prefix,somewhere_in_the_array; }
		assert i < a.Length by { reveal suffix_not_empty; }
	}
	// post1 (<==)
	if i < a.Length
	{
		assert key in a[..] by { assert a[i] == key; } // from post2 when "i < a.Length"
	}
}