method Main() /// 95 [redundant indices check - efficiency!]
{
	var q := [1,2,4,5,6,7,10,23];
	assert Sorted(q);
	assert HasAddends(q,10) by { assert q[2]+q[4] == 4+6 == 10; }
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
	assert (i == 2 && j == 4);
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}


method {:verify true} FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i, j := 0, |q| - 1;
	while i < j < |q| && q[i] + q[j] != x /// redundant indices check - efficiency!
	decreases j - i;
	invariant inv(q, x, i, j)
	{
		assert inv(q, x, i ,j) && i < j < |q| && q[i] + q[j] != x;
		i, j := find_new_borders(q, x, i ,j);
		assert inv(q, x, i ,j);
	}
	assert i < j < |q| && q[i] + q[j] == x;
}

method {:verify true} find_new_borders(q: seq<int>, x: int, i_prev: nat, j_prev: nat) returns (i: nat, j: nat)
requires inv(q, x, i_prev, j_prev) && q[i_prev] + q[j_prev] != x
ensures inv(q, x, i, j) && 0 <= j - i < j_prev - i_prev
{
	if q[i_prev] + q[j_prev] > x
	{
		has_addends_right_border(q, x, i_prev, j_prev);
		i, j := i_prev, j_prev - 1;
		assert inv(q, x, i, j);
	}
	else
	{
		has_addends_left_border(q, x, i_prev, j_prev);
		i, j := i_prev + 1, j_prev;
		assert inv(q, x, i, j);
	}

}

// ----- Functions & Predicates -----
predicate inv(q: seq<int>, x: int, i: nat, j: nat)
{
	Sorted(q) && 0 <= i < j < |q| && HasAddends(q[i..j+1], x)
}

// ----- Lemmas -----
lemma{:verify true} has_addends_right_border(q: seq<int>, x: int, i: nat, j: nat)
requires inv(q, x, i, j) && q[i] + q[j] > x
ensures inv(q, x, i, j-1) 
{
	assert Sorted(q);
	assert q[i] + q[j] > x;
	assert forall k:: i <= k < j ==> q[k] + q[j] > x;
	assert q[i..j] + [q[j]] == q[i..j+1];
	assert HasAddends(q[i..j], x);
	assert inv(q, x, i, j-1);
}

lemma{:verify true} has_addends_left_border(q: seq<int>, x: int, i: nat, j: nat)
requires inv(q, x, i, j) && q[i] + q[j] < x
ensures inv(q, x, i+1, j)
{}
