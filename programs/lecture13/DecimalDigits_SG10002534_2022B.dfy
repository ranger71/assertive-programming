/// length,fits computed correctlly; updating a[..length] instead of a[start..start+length]
/// unverified lemma ensures "false" and from then on, Dafny is no longer helpful
/// 40%
method Main()
{
	var a := new nat[3] [0, 0, 0];
	var n, start := 8, 0;
	assert NumberOfDecimalDigits(n, 1);
	ghost var q0 := a[..];
	var len, fits := IntToString(n, a, start);
	assert DecimalDigits(a[start..start+len], n);
	assert fits && len == 1 && a[0] == 8 && a[1..] == q0[1..];
}

predicate IsSingleDecimalDigit(d: nat) { 0 <= d && d <= 9 }

predicate NoLeadingZeros(q: seq<nat>)
	requires |q| != 0
{
	q[0] == 0 ==> |q| == 1
}

predicate IsDecimal(q: seq<nat>)
{
	|q| != 0 && (forall d :: d in q  ==> IsSingleDecimalDigit(d)) && NoLeadingZeros(q)
}

function SeqToNat(q: seq<nat>): nat
	requires IsDecimal(q)
{
	if |q| == 1 then q[0] else SeqToNat(q[..|q|-1])*10+q[|q|-1]
}

predicate DecimalDigits(q: seq<nat>, n: nat)
{/// when q == [] this is false
	IsDecimal(q) && SeqToNat(q) == n
}

predicate NumberOfDecimalDigits(n: nat, length: nat)
	decreases length
{
	(length == 1 && IsSingleDecimalDigit(n)) ||
	(length > 1 && !IsSingleDecimalDigit(n) && NumberOfDecimalDigits(n/10, length-1)) 
}

predicate Pre(n: nat, q: seq<nat>, start: nat)
{
	start < |q|
}

predicate Post(n: nat, q: seq<nat>, q0: seq<nat>, start: nat, length: nat, fits: bool)
	requires |q| == |q0|
{
	NumberOfDecimalDigits(n, length) &&
	fits == (start + length <= |q|) &&
	(fits ==> q[..start] == q0[..start] && DecimalDigits(q[start..start+length], n) && q[start+length..] == q0[start+length..]) &&
	(!fits ==> q == q0)
}

// TODO: provide an implementation; NO NEED to document the proof obligations
method IntToString(n: nat, a: array<nat>, start: nat) returns (length: nat, fits: bool)
	requires Pre(n, a[..], start)
	ensures Post(n, a[..], old(a[..]), start, length, fits)
	modifies a
	{
		length := GetNumOfDig(n);
		fits := start + length <= a.Length;
		if fits
		{
			SetDecDigNewArray(n, a, start, length);
		}
	}

method GetNumOfDig(n: nat) returns (length: nat)
	ensures NumberOfDecimalDigits(n,length)
	decreases n
{	
	if 0 <= n <= 9 //number has only 1 digit
	{	
		length := 1;
	}
	else
	{
		var div := GetNumOfDig(n/10);
		length := 1 + div;
	}
}

method {:verify true} SetDecDigNewArray(n: nat, a: array<nat>, start: nat, length: nat)
    requires start + length <= |a[..]|
    ensures Post(n, a[..], old(a[..]), start, length, true);
    modifies a
{
	var sum := 0;
	var base := 10;
	var i := 0;
    assert DecimalDigits(a[start..(start+i)], sum) by {BeginInvariant(a[start..(start+i)], sum);}
	/// due to the incorrect lemma Dafny will not complain even if we remove the rest of the code;
	/// is it correct? the digits? not clear; the written portion of "a"? incorrect!
	while i < length
		decreases length - i
		invariant DecimalDigits(a[start..(start+i)], sum); /// must limit the value of "i"
	{/// is this correct? why?
		var div := IterativeIntExpo(base, length - 1 - i); /// from the other program /// complexity!!!!!
		var p := sum * base + (n / div) % base; //building the number from end to start
		sum := p;
        var dig := sum % base; //unity digit
		a[i] := dig; // check - a[length-1-i] /// start writing from a[0] instead of a[start]
        i := i + 1;
	}
}

lemma {:verify false} BeginInvariant(a: seq<nat>, sum:nat)
	requires a[..] == []
	requires sum == 0
	ensures DecimalDigits(a, sum) /// == false
{
// At the beginning the sequence 'a' is empty so the sum is 0.
}

function RecursiveIntExpo(x: int, y: nat): int
	decreases y
{
	if y == 0 then 1 else x * RecursiveIntExpo(x, y-1)
}

// TODO: implement iteratively; NO NEED to document the proof obligations
method IterativeIntExpo(x: int, y: nat) returns (z: int)
	ensures z == RecursiveIntExpo(x, y)
	{
		var i := 0;
		var p := 1;
		z := 1;
  		while (i < y)
			invariant 0 <= i <= y;
			invariant z == RecursiveIntExpo(x, i);
 		{
			i := i + 1;
			p := z * x;
			z := p;
  		}
	}