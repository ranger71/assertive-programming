method Main() {
    var x := Sqrt(9);
    assert x == 3;
    print "The floor of the non-negative square root of 9 is ", x, "\n";
    x := Sqrt(10);
    assert x == 3;
    print "The floor of the non-negative square root of 10 is ", x, "\n";
}

method Sqrt(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
	assert n >= 0;
	// ==>?
	assert 0*0 <= n < (n+1)*(n+1);
	var a, b := 0, n+1;
	assert a*a <= n < b*b;
	while b != a+1
		invariant a*a <= n < b*b

	assert a*a <= n < b*b;
	assert b == a+1;
	// ==>?
	assert a*a <= n < (a+1)*(a+1);
	res := a;
	assert res*res <= n < (res+1)*(res+1);
}