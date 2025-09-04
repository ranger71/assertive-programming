method Main() {
    //var x := Sqrt(-9); // a precondition might not hold!
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
    // ==>
    assert 0*0 <= n;
    res := 0;
    assert res*res <= n;
    while !(n < (res+1)*(res+1))
        invariant res*res <= n
        decreases n - res*res
    {
        assert res*res <= n;
        assert !(n < (res+1)*(res+1));
        // ==>
        assert (res+1)*(res+1) <= n;
        res := res+1;
        assert res*res <= n;
    }
    assert res*res <= n < (res+1)*(res+1);
}

method Sqrt'(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
    res := 0;
    while !(n < (res+1)*(res+1))
        invariant res*res <= n
        decreases n - res*res
    {
        ghost var V0 := n - res*res;
        assert res*res <= n;
        assert !(n < (res+1)*(res+1));
        assert V0 == n - res*res;
        // ==>?
        assert 0 <= n - (res+1)*(res+1) < V0;
        res := res+1;
        assert 0 <= n - res*res < V0;
    }
}

method Sqrt''(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
    res := 0;
    while !(n < (res+1)*(res+1))
        invariant res*res <= n
        decreases n - res*res
    {
        res := res+1;
    }
}

method Sqrt_from_class_with_a_weaker_invariant(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
    res := 0;
    while res*res <= n
        // this invariant is weaker than the one we had in class, and it is correct even on entry to the loop
        invariant res == 0 || (res-1)*(res-1) <= n
        decreases n - res
    {
        res := res+1;
    }
    res := res-1;
}

method Sqrt_from_class_with_a_different_initial_value(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
    res := 1; // instead of the 0 in class which did not establish the invariant in the case of n == 0 
    while res*res <= n
        invariant (res-1)*(res-1) <= n
        decreases n - res
    {
        res := res+1;
    }
    res := res-1;
}

method Sqrt_Down_Loop(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
    assert n >= 0;
    // ==>
    assert n < (n+1)*(n+1);
    assert 0 <= n;
    res := n;
    assert n < (res+1)*(res+1);
    assert 0 <= res;
    while n < res*res
        invariant n < (res+1)*(res+1)
        invariant 0 <= res
        decreases res 
    {
        assert n < (res+1)*(res+1);
        assert 0 <= res;
        assert n < res*res;
        // ==>?
        assert n < (res-1+1)*(res-1+1);
        assert 0 <= res-1;
        assert 0 <= res-1 < res;
        ghost var V0 := res;
        assert n < (res-1+1)*(res-1+1);
        assert 0 <= res-1;
        assert 0 <= res-1 < V0;
        res := res-1;
        assert n < (res+1)*(res+1);
        assert 0 <= res;
        assert 0 <= res < V0;
    }
    assert res*res <= n < (res+1)*(res+1);
}

method Sqrt_Down_Loop'(n: int) returns (res: int)
    requires n >= 0
    ensures res*res <= n < (res+1)*(res+1)
{
    res := n;
    while n < res*res
        invariant n < (res+1)*(res+1)
        invariant 0 <= res
        decreases res 
     {
         res := res-1;
     }
}
