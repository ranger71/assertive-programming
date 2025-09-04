method Main() {
    //var x := Sqrt(-9); // a precondition might not hold!
    var x := Sqrt(9);
    assert x == 3;
    print "The floor of the non-negative square root of 9 is ", x, "\n";
    x := Sqrt(10);
    assert x == 3;
    print "The floor of the non-negative square root of 10 is ", x, "\n";
}

method {:verify false} Sqrt(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
    assert n >= 0;
    // ==>?
    assert (0-1)*(0-1) <= n;
    res := 0;
    assert (res-1)*(res-1) <= n;
    while res*res <= n
        invariant (res-1)*(res-1) <= n
    {
        res := res+1;
        assert (res-1)*(res-1) <= n;
    }
    assert (res-1)*(res-1) <= n < (res-1+1)*(res-1+1);
    res := res-1;
    assert res*res <= n < (res+1)*(res+1);
}