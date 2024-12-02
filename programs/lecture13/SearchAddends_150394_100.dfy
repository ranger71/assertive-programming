method Main() /// 100
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
	LemmaInit(q, 0, |q|-1, x);
	i, j := FindIndexes(q, x);
	LemmaResult(q, i, j, x);
}

predicate Inv(q: seq<int>, i: nat, j: nat, x: int)
{
	0 <= i < j < |q| && Sorted(q) && HasAddends(q[i..j+1], x)
}

lemma LemmaInit(q: seq<int>, i: nat, j: nat, x: int)
	requires |q| >= 2 && Inv(q, i, j, x)  
	ensures 0 <= i < j < |q| 
{}	


lemma LemmaResult(q: seq<int>, i: nat, j: nat, x: int)
	requires Inv(q, i, j, x) && q[i] + q[j] == x
	ensures 0 <= i < j < |q| && q[i]+q[j] == x
{}

method FindIndexes(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires |q| >= 2 && Inv(q, 0, |q|-1, x)
	ensures Inv(q, i, j, x) && q[i] + q[j] == x
{
	i := 0;
	j := |q|-1;

	while q[i] != x - q[j]
		invariant Inv(q, i, j, x)
		decreases j-i 
	{
		i,j := Find(q, i, j, x);
	}
}

method Find(q: seq<int>, a: nat, b: nat, x: int) returns (i: nat, j: nat)
	requires Inv(q, a, b, x) && q[a] != x - q[b]
	ensures Inv(q, i, j, x) && 0 <= j-i < b-a
{
	// case 1: q[a]+q[b]<x
	// not changing b, increasing a, to increase the result
	if q[a]+q[b] < x
	{
		i := FindNewI(q,a,b,x);
		j := b;
	}
	// case 2: q[a]+q[b]>x
	// not changing a, decreasing b, to decrease the result
	else
	{
		i := a;
		j := FindNewJ(q,a,b,x);
	}
}
method FindNewI(q: seq<int>, a: nat, j: nat, x: int) returns (i: nat)
	requires Inv(q, a, j, x) && q[a] + q[j] < x
	ensures Inv(q, i, j, x) && a < i && i < j
{
	LemmaOldI(q, a, j, x);
	//increaing i by 1
	i := a+1;
}

lemma LemmaOldI(q: seq<int>, i: nat, j: nat,  x: int)
	requires Inv(q, i, j, x) && q[i] + q[j] < x
	ensures Inv(q, i+1, j, x) 
{}

method FindNewJ(q: seq<int>, i: nat, b: nat, x: int) returns (j: nat)
	requires Inv(q, i, b, x) && q[i] + q[b] > x 
	ensures Inv(q, i, j, x) && 0 <= j < b
{
	LemmaOldJ(q, i, b, x);
	// decreasing j by 1
	j := b-1;
}

lemma LemmaOldJ(q: seq<int>, i: nat, j: nat, x: int)
	requires Inv(q, i, j, x) && q[i] + q[j] > x 
	ensures Inv(q, i, j-1, x) 
{
	assert HasAddends(q[i..j], x) by { 
		assert q[i..j+1] == q[i..j]+[q[j]];
		forall a | a >= i && a < j ensures q[a]+q[j] != x {}
	}
}

