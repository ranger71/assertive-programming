method Main() /// 75 [key in q in the code; binary-search for one occurence followed by two linear searches; linear search when key !in q] 
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

method FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: left <= i < right ==> q[i] == key
	ensures forall i :: right <= i < |q| ==> q[i] > key
    {
        // q is empty:
        if |q|==0
        {
            left, right := 0, 0;
            return;
        }

        assert |q|>0 ;

        if key in q /// a linear-time operation!
        {
            var result := BinarySearch(q, key);
            left, right := result, result+1;
            
            while (left==1 && q[0]==key) || (left>1 && q[left-1]==key)
            invariant q[left]==key
            decreases left
            {
                left := left-1;
            }

            while (right==|q|-1 && q[right]==key) || (right<|q|-1 && q[right]==key)
            invariant right<=|q| && q[right-1]==key
            decreases |q|-right
            {
                right := right+1;
            }
        }

        else // if key not in q
        {
            //all elements are smaller than key:
            if q[|q|-1] < key
            {
                left, right := |q|, |q|;
                return;
            }
            
            //all elements are bigger than key:
            else if q[0] > key
            {
                left, right := 0, 0;
                return;
            }

            else
            {
                assert q[0] <= key <= q[|q|-1];
                left := 0 ;
                while q[left]<key
                invariant left<|q| && forall i :: 0 <= i < left ==> q[i] < key
                decreases |q|-left
                {
                    left := left+1; /// linear
                }
                right := left;
                return;
            }
        } 
    } // end of FindRange

    method BinarySearch(q: seq<int>, key: int) returns (result: int)
    requires Sorted(q)
    ensures 0 <= result ==> result < |q| && q[result] == key
    ensures result < 0 ==> key !in q[..]
    {
        var low, high := 0, |q|;
        while low < high
        invariant 0 <= low <= high <= |q|
        invariant key !in q[..low] && key !in q[high..]
        decreases high-low
        {
            var mid := (low + high) / 2;
            if key < q[mid] 
            {
                high := mid;
            } 
            else if q[mid] < key 
            {
                low := mid + 1;
            } 
            else 
            {
                return mid;
            }
        }
        return -1;
    } // end of binarySearch