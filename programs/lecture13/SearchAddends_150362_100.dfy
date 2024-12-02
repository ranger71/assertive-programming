method Main()
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
	assert i == 2 && j == 4;
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i, j := 0, |q|-1;
	while q[i] + q[j] != x
	invariant 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x)
	decreases j-i
	{
		if q[i] + q[j] < x
		{
			i := i + 1;
		}
		else{
			IndexJIsNotOneOfTheAddends(q, i, j, x);
			j := j -1 ;
			assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x);
		}
		assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x);
	}
}


lemma IndexJIsNotOneOfTheAddends(q: seq<int>, i: nat, j:nat, x:int)
	requires 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x) && q[i] + q[j] > x
	ensures 0 <= i < j - 1 <|q| && Sorted(q) && HasAddends(q[i..j+1-1], x)
{
	assert 0 <= i < j - 1 <|q| by {
		assert 0 <= i < j <|q|; 
		assert HasAddends(q[i..j+1], x);
	}
	assert HasAddends(q[i..j+1-1], x) by {
		assert HasAddends(q[i..j+1], x);
		assert q[i..j+1] == q[i..j]+[q[j]];
		forall k | i <= k < j ensures q[k] + q[j] != x {
			calc {
				q[k] + q[j];
				>= {assert k >= i && Sorted(q);}
				q[i] + q[j];
				>
				x;
			}
		} 
	}
}


method FindAddends'(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i, j := 0, |q|-1;
	while q[i] + q[j] != x
	invariant 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x)
	decreases j-i
	{
		assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x) && q[i] + q[j] != x;
		if q[i] + q[j] < x
		{
			assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x) && q[i] + q[j] < x;
			assert 0 <= i + 1 < j <|q| && Sorted(q) && HasAddends(q[i+1..j+1], x);
			i := i + 1; 
			assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x);
		}
		else{
			assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x) && q[i] + q[j] > x;
			IndexJIsNotOneOfTheAddends(q, i, j, x);
			assert 0 <= i < j - 1 <|q| && Sorted(q) && HasAddends(q[i..j+1-1], x);
			j := j -1 ;
			assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x);
		}
		assert 0 <= i < j <|q| && Sorted(q) && HasAddends(q[i..j+1], x);
	}
}