/* inductive datatypes + pattern matching + recursive methods + structural order */
datatype NatList = Empty | Cons(head: nat, tail: NatList)

method Main() {
	var nl := Cons(6,Cons(8,Cons(4,Empty)));
	print "\nThe total sum of all natural numbers in the list Cons(6,Cons(8,Cons(4,Empty))) is ";
	var n := ComputeSumList(nl);
	print n;
	assert n == SumList(nl) == 6 + 8 + 4;

	var nl2 := Cons(3,nl);
	print "\nThe total sum of all natural numbers in the list Cons(3,Cons(6,Cons(8,Cons(4,Empty)))) is ";
	var n2 := ComputeSumList(nl2);
	print n2;
	assert n2 == 3 + 6 + 8 + 4 by {
		// correctness of this assertion was not obvious, for the Dafny verifier,
		// so it needed some help (added after the lecture)
		calc {
			n2;
		==
			SumList(nl2);
		==
			3 + SumList(nl);
		==
			3 + n;
		==
			3 + 6 + 8 + 4;
		}
	}

	print "\nThe total sum of all natural numbers in the list Cons(3,Cons(6,Cons(8,Cons(4,Empty)))) is ";
	var n3 := ComputeSumListIter(nl2); // compute iteratively this time, instead of recursively
	print n3;
	assert n3 == n2 == 3 + 6 + 8 + 4;
}

ghost function SumList(nl: NatList): nat
	decreases nl
{
	match nl {
		case Empty => 0
		case Cons(n',nl') => n'+SumList(nl')
	}
}

method ComputeSumList(nl: NatList) returns (n: nat)
	ensures n == SumList(nl)
	decreases ListLength(nl)
	//another possible variant (structural order):
	//decreases nl
{
	if nl == Empty {
		assert nl == Empty;
		// ==>
		assert 0 == SumList(nl);
		n := 0;
		assert n == SumList(nl);
	}
	else {
		assert nl != Empty;
		// ==>? yes! by the definition of the ghost function SumList on non-empty lists
		assert nl.head + SumList(nl.tail) == SumList(nl);
		assert 0 <= ListLength(nl.tail) < ListLength(nl) by {
			TerminationForTheRecursion(nl);
		}
		var sum_of_tail := ComputeSumList(nl.tail); // same as the ghost := SumList(nl.tail)
		assert nl.head + sum_of_tail == SumList(nl);
		n := nl.head + sum_of_tail;
		assert n == SumList(nl);
	}
	assert n == SumList(nl);
}

function ListLength(nl: NatList): int
	decreases nl
{
	match nl {
		case Empty => 0
		case Cons(n',nl') => 1+ListLength(nl')
	}
}

// we wouldn't need the following lemma if we were to use the alternative variant mentioned above
// (using structureal order instead of an integer function for the variant);
// still, I prefer to leave our original variant and include a detailed proof here,
// as another example for proof writing
lemma TerminationForTheRecursion(nl: NatList)
	requires nl.Cons?
	ensures 0 <= ListLength(nl.tail) < ListLength(nl)
{
	assert 0 <= ListLength(nl.tail) by { NonNegativeLength(nl.tail); }
	assert ListLength(nl.tail) < ListLength(nl) by {
		calc {
			ListLength(nl);
		== { assert nl == Cons(nl.head, nl.tail); }
			ListLength(Cons(nl.head, nl.tail));
		== // def. for a non-empty list
			1+ListLength(nl.tail);
		> // arithmetic
			ListLength(nl.tail);
		}
	}
}

// a simple property, with one more example of proof by induction
lemma NonNegativeLength(nl: NatList)
	ensures 0 <= ListLength(nl)
	decreases nl
{
	match nl {
	case Empty =>
		assert ListLength(nl) == 0;
	case Cons(n', nl') =>
		calc {
			0;
		<= { NonNegativeLength(nl'); } // induction hypothesis
			ListLength(nl');
		<=
			1+ListLength(nl');
		==
			ListLength(nl);
		}
	}
}

method ComputeSumListIter(nl: NatList) returns (n: nat)
	ensures n == SumList(nl)
{
	var nl1 := nl;
	n := 0;
	while nl1 != Empty
		invariant n == SumList(nl) - SumList(nl1)
		decreases nl1
	{
		assert nl1.Cons?;
		assert n == SumList(nl) - SumList(nl1);
		assert nl1 != Empty;
		assert nl1 == Cons(nl1.head, nl1.tail);
		// ==>
		assert n+nl1.head == SumList(nl) - SumList(nl1.tail);
		n, nl1 := n+nl1.head, nl1.tail;
		assert n == SumList(nl) - SumList(nl1);
	}
}
