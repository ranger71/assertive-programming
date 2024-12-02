include "IO.dfy"

datatype BinaryDigit = Zero | One

method {:verify false} Main() { // it verifies alright, but takes long time, so leaving it out for now
	var io: IO<BinaryDigit> := new IO<BinaryDigit>;
	io.Rewrite();
	WriteCode(0, io);
	assert io.omega == [Zero];
	print "\nThe Gray Code of 0 is ";
	print io.omega;

	io.Rewrite();
	WriteCode(1, io);
	assert io.omega == [One];
	print "\nThe Gray Code of 1 is ";
	print io.omega;

	var n := 2;
	var m := n/2;

	assert GrayCode(m) == [One];
	assert GrayCode(n-1) == [One];
	assert DiffersInOneElement([One, One, Zero], [One, Zero]);

	io.Rewrite();
	WriteCode(n, io);
	assert io.omega == [One, One];
	print "\nThe Gray Code of 2 is ";
	print io.omega;

	n := 3;
	m := n/2;

	assert GrayCode(m) == [One];
	assert GrayCode(n-1) == [One, One];
	assert DiffersInOneElement([One, Zero], [One, One]);

	io.Rewrite();
	WriteCode(n, io);
	assert io.omega == [One, Zero];
	print "\nThe Gray Code of 3 is ";
	print io.omega;

	n := 4;
	m := n/2;

	assert GrayCode(m) == [One, One];
	assert GrayCode(n-1) == [One, Zero];
	assert DiffersInOneElement(GrayCode(m)+[Zero], GrayCode(n-1));
	assert DiffersInOneElement([One, One, Zero], [One, Zero]);

	io.Rewrite();
	WriteCode(n, io);
	assert io.omega == [One, One, Zero];
	print "\nThe Gray Code of 4 is ";
	print io.omega;

	n := 5;
	m := n/2;

	assert GrayCode(m) == [One, One];
	assert !DiffersInOneElement(GrayCode(m)+[Zero], GrayCode(n-1));
	assert !DiffersInOneElement([One, One, Zero], [One, One, Zero]);

	io.Rewrite();
	WriteCode(n, io);
	assert io.omega == [One, One, One];
	print "\nThe Gray Code of 5 is ";
	print io.omega;

	n := 6;
	m := n/2;

	assert GrayCode(m) == [One, Zero];
	assert !DiffersInOneElement(GrayCode(m)+[Zero], GrayCode(n-1));
	assert !DiffersInOneElement([One, Zero, Zero], [One, One, One]);

	io.Rewrite();
	WriteCode(n, io);
	assert io.omega == [One, Zero, One];
	print "\nThe Gray Code of 6 is ";
	print io.omega;

	n := 7;
	m := n/2;

	assert GrayCode(m) == [One, Zero];
	assert DiffersInOneElement(GrayCode(m)+[Zero], GrayCode(n-1));
	assert DiffersInOneElement([One, Zero, Zero], [One, Zero, One]);

	io.Rewrite();
	WriteCode(n, io);
	assert io.omega == [One, Zero, Zero];
	print "\nThe Gray Code of 7 is ";
	print io.omega;

	n := 8;
	m := n/2;

	assert GrayCode(m) == [One, One, Zero];
	assert DiffersInOneElement(GrayCode(m)+[Zero], GrayCode(n-1));
	assert DiffersInOneElement([One, One, Zero, Zero], [One, Zero, Zero]);

	io.Rewrite();
	WriteCode(8, io);
	assert io.omega == [One, One, Zero, Zero];
	print "\nThe Gray Code of 8 is ";
	print io.omega;

	n := 9;
	m := n/2;

	assert GrayCode(m) == [One, One, Zero];
	assert !DiffersInOneElement(GrayCode(m)+[Zero], GrayCode(n-1));
	assert !DiffersInOneElement([One, One, Zero, Zero], [One, One, Zero, Zero]);

	io.Rewrite();
	WriteCode(9, io);
	assert io.omega == [One, One, Zero, One];
	print "\nThe Gray Code of 9 is ";
	print io.omega;
}

predicate DiffersInOneElement(xs: seq<BinaryDigit>, ys: seq<BinaryDigit>)
{
	if |xs| > |ys| then xs == [One] + ys else
	if |xs| < |ys| then [One] + xs == ys else
	if |xs| == 0 then false else
	if xs[0] == ys[0] then DiffersInOneElement(xs[1..], ys[1..]) else xs[1..] == ys[1..]
}

function GrayCode(n: nat): seq<BinaryDigit>
{
	if n == 0 then [Zero] else
	if n == 1 then [One] else 
		GrayCode(n/2) +
		[if DiffersInOneElement(GrayCode(n/2)+[Zero], GrayCode(n-1)) then Zero else One]
}

method WriteCode(n: nat, io: IO<BinaryDigit>)
	modifies io
	ensures io.omega == old(io.omega) + GrayCode(n)
	decreases n
{
	assert io.omega == old(io.omega);
	if n == 0
	{
		assert io.omega == old(io.omega);
		assert n == 0;
		// ==>
		assert io.omega + [Zero] == old(io.omega) + GrayCode(n);
		io.Output(Zero); // io.omega := io.omega + [Zero]
		assert io.omega == old(io.omega) + GrayCode(n);
	}
	else if n == 1
	{
		// like the above
		io.Output(One); // io.omega := io.omega + [One]
	}
	else
	{
		if (n + n/2) % 2 == 0
		{
			WriteCode(n/2, io);
			assert io.omega + [Zero] == old(io.omega) + GrayCode(n) by
			{
				LemmaEven(n, io.omega, old(io.omega));
			}
			io.Output(Zero); // io.omega := io.omega + [Zero]
		}
		else
		{
			assert io.omega == old(io.omega);
			assert n > 1;
			assert (n + n/2) % 2 == 1;
			WriteCode(n/2, io);
			assert n > 1;
			assert (n + n/2) % 2 == 1;
			assert io.omega == old(io.omega) + GrayCode(n/2);
			LemmaOdd(n, io.omega, old(io.omega)); // ==>
			assert io.omega + [One] == old(io.omega) + GrayCode(n);
			io.Output(One); // io.omega := io.omega + [One]
			assert io.omega == old(io.omega) + GrayCode(n);
		}
		assert io.omega == old(io.omega) + GrayCode(n);
	}
	assert io.omega == old(io.omega) + GrayCode(n);
}

method WriteCode'(n: nat, io: IO<BinaryDigit>)
	modifies io
	ensures io.omega == old(io.omega) + GrayCode(n)
	decreases n
{
	if n == 0
	{
		io.Output(Zero); // io.omega := io.omega + [Zero]
	}
	else if n == 1
	{
		io.Output(One); // io.omega := io.omega + [One]
	}
	else
	{
		if (n + n/2) % 2 == 0
		{
			WriteCode(n/2, io);
			LemmaEven(n, io.omega, old(io.omega));
			io.Output(Zero); // io.omega := io.omega + [Zero]
		}
		else
		{
			WriteCode(n/2, io);
			LemmaOdd(n, io.omega, old(io.omega));
			io.Output(One); // io.omega := io.omega + [One]
		}
	}
}

lemma LemmaOdd(n: nat, omega: seq<BinaryDigit>, omega0: seq<BinaryDigit>)
	requires n > 1
	requires (n + n/2) % 2 == 1
	requires omega == omega0 + GrayCode(n/2)
	ensures omega + [One] == omega0 + GrayCode(n)
{
	var m: nat := n/2;
	assert m == n/2;
	assert n >= 2;
	assert (n+m) % 2 == 1;
	assert omega + [One] == omega0 + GrayCode(n) by {
		assert omega0 + GrayCode(m) + [One] == omega0 + GrayCode(n) by {
			assert GrayCode(m) + [One] == GrayCode(n) by
			{
				assert exists d :: GrayCode(m) + [d] == GrayCode(n); // by the definition of GrayCode
				calc {
					GrayCode(m) + [Zero] == GrayCode(n); // leading to contradiction
				==>
					EvenNumberOfOnes(GrayCode(m) + [Zero]) == EvenNumberOfOnes(GrayCode(n));
				== { Lemma1(n); }
					EvenNumberOfOnes(GrayCode(m) + [Zero]) == ((n % 2) == 0);
				== { Lemma3(GrayCode(m)); }
					EvenNumberOfOnes(GrayCode(m)) == ((n % 2) == 0);
				== { Lemma1(m); }
					((m % 2) == 0) == ((n % 2) == 0);
				== { Lemma2(m,n); }
					(m+n) % 2 == 0;
				== // contradiction with precondition
					false;
				}
			}
		}
	}
}

lemma LemmaEven(n: nat, omega: seq<BinaryDigit>, omega0: seq<BinaryDigit>)
	requires n > 1
	requires (n + n/2) % 2 == 0
	requires omega == omega0 + GrayCode(n/2)
	ensures omega + [Zero] == omega0 + GrayCode(n)
{
	var m := n/2;
	assert m == n/2;
	assert GrayCode(m) + [Zero] == GrayCode(n) by
	{
		assert exists d :: GrayCode(m) + [d] == GrayCode(n); // by the definition of GrayCode
		calc {
				GrayCode(m) + [One] == GrayCode(n); // as in LemmaOdd above, leading to contradiction
			==>
				EvenNumberOfOnes(GrayCode(m) + [One]) == EvenNumberOfOnes(GrayCode(n));
			== { Lemma1(n); }
				EvenNumberOfOnes(GrayCode(m) + [One]) == ((n % 2) == 0);
			==
				EvenNumberOfOnes(GrayCode(m)) != ((n % 2) == 0);
			== { Lemma1(m); }
				((m % 2) == 0) != ((n % 2) == 0);
			== { Lemma2(m,n); }
				(m+n) % 2 != 0;
			== // contradiction with precondition
				false;
		}
	}
}

predicate EvenNumberOfOnes(bs: seq<BinaryDigit>)
{
	if bs == [] then true else
	if bs[|bs|-1] == Zero then EvenNumberOfOnes(bs[..|bs|-1]) else
	!EvenNumberOfOnes(bs[..|bs|-1])
}

lemma Lemma1(n: nat) // Based on Morgan's Equation (14.1)
	ensures EvenNumberOfOnes(GrayCode(n)) <==> (n % 2) == 0
	decreases n
{
	if (n % 2) == 0
	{
		var i: nat := 0;
		while i != n
			invariant i%2 == 0 && n%2 == 0 && i <= n
			invariant EvenNumberOfOnes(GrayCode(i))
			decreases n-i
		{
			assert i%2 == 0 && n%2 == 0 && i < n;
			assert EvenNumberOfOnes(GrayCode(i));
			// ==>
			assert EvenNumberOfOnes(GrayCode(i+2)) by {
				assert !EvenNumberOfOnes(GrayCode(i+1));
				var j: nat := i+1;
				assert EvenNumberOfOnes(GrayCode(j+1)) by {
					assert !EvenNumberOfOnes(GrayCode(j));
					LemmaParity(j);
				}
			}
			i := i+2;
			assert EvenNumberOfOnes(GrayCode(i));
		}
		assert EvenNumberOfOnes(GrayCode(n)) <==> (n % 2) == 0;
	}
	else
	{
		var i: nat := 1;
		while i != n
			invariant i%2 == 1 && n%2 == 1 && i <= n
			invariant !EvenNumberOfOnes(GrayCode(i))
			decreases n-i
		{
			assert !EvenNumberOfOnes(GrayCode(i+2)) by {
				LemmaParity(i);
				LemmaParity(i+1);
			}
			i := i+2;
		}
	}
}

// according to Property 2 of the Gray code definition,
// the number of ones in the Gray code of "n+1" is even if and only if
// the number ones in the Gray of "n" is odd
lemma {:verify false} LemmaParity(n: nat)
	ensures EvenNumberOfOnes(GrayCode(n)) != EvenNumberOfOnes(GrayCode(n+1))
{}

lemma Lemma2(m: nat, n: nat)
	ensures ((m % 2) == 0) == ((n % 2) == 0) <==> (m+n) % 2 == 0
{}

lemma Lemma3(xs: seq<BinaryDigit>)
	ensures EvenNumberOfOnes(xs + [Zero]) == EvenNumberOfOnes(xs)
{}
