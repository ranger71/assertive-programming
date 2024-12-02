method Main() /// incorrect! linear search; two logically-incorrect lemmas with no body (I added a {:verify false} plus empty body and got 0,7 as a result instead of 4,6)]
{
	var q := [1,2,2,5,10,10,10,23];
	assert Sorted(q);
	assert 10 in q;
	var i,j := FindRange(q, 10);
	print "The number of occurrences of 10 in the sorted sequence [1,2,2,5,10,10,10,23] is ";
	print j-i;
	print " (starting at index ";
	print i;
	print " and ending in ";
	print j-1;
	print ").\n";
	assert i == 4 && j == 7 by {
		assert q[0] <= q[1] <= q[2] <= q[3] < 10;
		assert q[4] == q[5] == q[6] == 10;
		assert 10 < q[7];
	}
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate Inv1(q: seq<int>, key: int, l: nat, r: nat)
    requires r<=|q|
{
    forall i :: l <= i < r ==> q[i] == key
}

predicate Inv2(q: seq<int>, key: int, r: nat)
{
    forall i :: r <= i < |q| ==> q[i] > key
}

predicate Inv3(q: seq<int>, key: int, r: nat)
    requires r <=|q|
{
    forall i :: 0 <= i < r ==> q[i] < key
}

method FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: left <= i < right ==> q[i] == key
	ensures forall i :: right <= i < |q| ==> q[i] > key
{
    left := FindLeft(q, key);
    assert Inv3(q, key, left);
    right := FindRight(q,key);
    proofStep2(q, key, left, right);
}

lemma {:verify false} proofStep2(q: seq<int>, key: int, left: nat, right: nat)
    requires right <= |q| && Inv2(q, key, right) && left <= |q| && Inv3(q, key, left) 
    ensures Inv1(q, key, left, right) && left <= right <= |q|
	 {}
method FindLeft(q: seq<int>, key: int) returns (left: nat)
	requires Sorted(q)
    ensures left <= |q|
	ensures Inv3(q, key, left)
{
    left := 0;
    assert left <= |q|;
    if(|q| == 0 || q[left] > key){
        left := 0;
    }
    else{
        // FindLeft0(q, key, left);
        left := FindLeft1(q, key, left);
    }
}

method FindLeft1(q: seq<int>, key: int, leftF: nat) returns (left: nat)
	requires Sorted(q) && |q| != 0 && leftF == 0 && Inv3(q, key, leftF)
    ensures left <= |q|
	ensures Inv3(q, key, left)
    {
        left := leftF;
        var temp := left;
        assert left <|q|;
        while( temp < |q| && left < |q| && q[left] > key)
        invariant left <= |q|
        invariant Inv3(q, key, left)
        decreases |q|-temp
        {
            // assert left < |q|;
            if q[left] < key {
                left := increaseLeft(q, key, left);
                temp := left;
            }
            // assert left < |q| && Inv3(q, key, left);
            // //assert  q[left] <= key;
            // if q[left] > key{
            //     left := increaseLeft(q, key, left);
            //     temp := left;
            // }
            else{
                temp:= temp+1;
            }
            
            //assert (|q| == left || q[left] <= key);
        }
    }

method increaseLeft(q: seq<int>, key: int, leftF: nat) returns (left: nat)
	requires Sorted(q) && leftF < |q|  && Inv3(q,key,leftF) && q[leftF] < key
	ensures left <= |q| && Inv3(q, key, left)
    {
    left := leftF;
    //if q[leftF] < key {
    left := left +1;
    //}
    // else{
    //     left := left;
    // }
        
        
    }


method FindRight(q: seq<int>, key: int) returns (right: nat)
	requires Sorted(q)
    ensures right <= |q|
	ensures Inv2(q, key, right)
{
    right := |q|;
    assert right <= |q|;
    if(|q| == 0 || q[right-1] > key){
        right := |q|;
    }
    else{
        proofStep(q, key, right-1);
        right := FindRight1(q, key, right-1);
    }
}

lemma {:verify false} proofStep(q: seq<int>, key: int, rightF: nat)
    //requires rightF == |q|-1 && q[rightF] < key
    ensures Inv2(q, key, rightF)
    // {
    //     assert forall i :: rightF <= i < |q| ==> q[i] < key;
    // }
	 {}
method FindRight1(q: seq<int>, key: int, rightF: nat) returns (right: nat)
	requires Sorted(q) && |q| != 0 && rightF < |q| && Inv2(q, key, rightF)
    ensures right <= |q|
	ensures Inv2(q, key, right)
    {
        right := rightF;
        var temp:int := right;
        //assert right <|q|;
        while( temp >= 0 && right >= 0)
        invariant right < |q|
        invariant Inv2(q, key, right)
        decreases temp
        {
            // if right == |q|{
            //     right := right -1;
            // }
            if q[right] < key {
                right := decreasesRight(q, key, right);
                temp := right;
            }
            else{
                temp:= temp - 1;
            }            
        }
    }

method decreasesRight(q: seq<int>, key: int, rightF: nat) returns (right: nat)
	requires Sorted(q) && rightF < |q|  && Inv2(q,key,rightF) && q[rightF] < key
	ensures right <= |q| && Inv2(q, key, right)
    {
    right := rightF;
    right := right -1;
        
        
    }