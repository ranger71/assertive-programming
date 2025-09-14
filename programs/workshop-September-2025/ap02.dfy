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
