method Main() {
    var x, y, z := 5, 8, -2;
    print "Before swapping:         x is ", x, " y is ", y, " and z is ", z ,"\n";
    x, y := Swap(x, y);
    assert x == 8 && y == 5 && z == -2;
    print "After swapping x and y:  x is ", x, " y is ", y, " and z is ", z ,"\n";

    y, z := Swap(y, z);
    assert x == 8 && y == -2 && z == 5;
    print "After swapping y and z:  x is ", x, " y is ", y, " and z is ", z ,"\n";

    x, y := Sort2(x, y);
    assert x == -2 && y == 8 && z == 5;
    print "After sorting x and y:   x is ", x, " y is ", y, " and z is ", z ,"\n";

    x, z := Swap(x, z);
    assert x == 5 && y == 8 && z == -2;
    print "After swapping x and z:  x is ", x, " y is ", y, " and z is ", z ,"\n";

    ghost var x0, y0, z0 := x, y, z;
    x, y, z := Sort3(x, y, z);
    assert x == -2 && y == 5 && z == 8 by {
        // Exercise: make the proof more explicit, considering
        // also the other postcondition that x <= y <= z
        assert multiset({x0, y0, z0}) == multiset{5, 8, -2} ==
            multiset{-2, 5, 8} == multiset({x, y, z});
    }
    print "After sorting x, y, z:    x is ", x, " y is ", y, " and z is ", z ,"\n";
}

method Swap(a0: int, b0: int) returns (a: int, b: int)
    ensures a == b0 && b == a0
{
    assert b0 == b0 && a0 == a0;
    a := b0;
    assert a == b0 && a0 == a0;
    b := a0;
    assert a == b0 && b == a0;
}

method Sort2(a0: int, b0: int) returns (a: int, b: int)
    ensures (a == a0 && b == b0) || (a == b0 && b == a0)
    ensures a <= b
{
    if a0 <= b0 {
        assert a0 <= b0;
        // ==>?
        assert (a0 == a0 && b0 == b0) || (a0 == b0 && b0 == a0);
        assert a0 <= b0;
        a := a0;
        assert (a == a0 && b0 == b0) || (a == b0 && b0 == a0);
        assert a <= b0;
        b := b0;
        assert (a == a0 && b == b0) || (a == b0 && b == a0);
        assert a <= b;
    }
    else {
        assert !(a0 <= b0);
        // ==>?
        assert (b0 == a0 && a0 == b0) || (b0 == b0 && a0 == a0);
        assert b0 <= a0;
        a := b0;
        assert (a == a0 && a0 == b0) || (a == b0 && a0 == a0);
        assert a <= a0;
        b := a0;
        assert (a == a0 && b == b0) || (a == b0 && b == a0);
        assert a <= b;
    }
    assert (a == a0 && b == b0) || (a == b0 && b == a0);
    assert a <= b;
}

method Sort2'(a0: int, b0: int) returns (a: int, b: int)
    ensures (a == a0 && b == b0) || (a == b0 && b == a0)
    ensures a <= b
{
    if a0 <= b0 {
        a := a0;
        b := b0;
    }
    else {
        a := b0;
        b := a0;
    }
}


method Sort3(a0: int, b0: int, c0: int) returns (a: int, b: int, c: int)
    ensures a <= b <= c
    ensures multiset({a0, b0, c0}) == multiset({a, b, c})
    // Exercise: strengthen the postcondition (as in Sort2), implement and prove
