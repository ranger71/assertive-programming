method Main() /// 90 [redundant check, inv could be strengthened for that, bad indentation]
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
		i := 0; 
		j := |q| - 1;

        while (i < j) /// always true
			invariant i<= j < |q| && HasAddends(q[i..j+1], x) /// could be stronger, to show the loop guard is redundant
		{
            if (q[i] + q[j] == x)
			{
				return;
			}        
            else if (q[i] + q[j] < x){
				lemma_sumSmaller(q, i, j, x);
                i := i + 1;
			}
            else{
				lemma_sumBigger(q, i, j, x);
                j := j - 1;
			}
		}
	}

lemma lemma_sumSmaller (q: seq<int>, i: nat, j:nat, x:int)
	requires i <= j < |q| && HasAddends(q[i..j+1], x); 			// Inv + gaurd
	requires Sorted(q) && HasAddends(q, x)						// pre condition
	requires q[i] + q[j] < x									// else if condition
	ensures i+1 <= j < |q| && HasAddends(q[i+1..j+1], x)
	{}

lemma lemma_sumBigger (q: seq<int>, i: nat, j:nat, x:int)
	requires i <= j < |q| && HasAddends(q[i..j+1], x); 			// Inv + gaurd
	requires Sorted(q) && HasAddends(q, x)						// pre condition
	requires x < q[i] + q[j] 									// else condition
	ensures i <= j-1 < |q| && HasAddends(q[i..j], x)
	{
		// sum is too big, need to take smaller element 
		// array is sorted => q[j-1] < q[j]
		assert i <= j < |q| && q[..j] < q[..j+1]; 	
		assert i <= j-1 < |q| && HasAddends(q[i..j], x);
	}

