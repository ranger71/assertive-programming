/* sets, function type + lambda expressions, datatypes + pattern matching, recursive methods */
method Main() {
	assert {4,3,4} == {3,4} == {4,3};
	var s := {4, 5, 67, 21, 8, 9};
	var x;
	x := FindElement(s, IsEven);
	assert x == 4 || x == 8;
	print "An even element in the set {4, 5, 67, 21, 8, 9}:\n";
	print x;
	print "\n";
	x := FindElement(s, e => e % 2 == 0);
	assert x == 4 || x == 8;
	print x;
	print "\n";
	x := FindEven(s);
	assert x == 4 || x == 8;
	print x;
	print "\n";

	x := FindElement({3,7}, x => x%2 == 1);
	assert x == 3 || x == 7;

	var db: Database<int,int> := [Empty, Full(0,0), Full(1,1), Full(2,10), Full(3,11), Full(4,100), Full(5,101)];
	print "The key 5 is associated with: ";
	var d:= Find(db, 5);
	assert d == 101;
	print d;
}

predicate IsEven(x: int) { x % 2 == 0 }

method FindEven(s: set<int>) returns (e: int)
	requires exists x :: x in s && IsEven(x)
	ensures e in s && IsEven(e)
{
	assert exists x :: x in s && IsEven(x); // from *our* precondition
	// ==>?
	assert exists x :: x in s && IsEven(x); // the precondition of FindElement must hold
	e := FindElement(s, IsEven);
	assert e in s && IsEven(e); // we get this from FindElement's postcondition
	// ==>
	assert e in s && IsEven(e); // this is *our* postcondition
}

method FindElement'(s: set<int>, p: int -> bool) returns (e: int)
	requires exists x :: x in s && p(x)
	ensures e in s && p(e)
	decreases |s|
{
	e :| e in s;
	if !p(e) {
		e := FindElement(s-{e}, p);
	}
}

// a first example of a recursive method, documenting all proof obligations
// using assertions; exercise: add the relevant lemma specifications
method {:verify false} FindElement(s: set<int>, p: int -> bool) returns (e: int)
	requires exists x :: x in s && p(x)
	ensures e in s && p(e)
	decreases |s| // Dafny guesses "s" which is also good: it means "strict subset"
{
	assert exists x :: x in s && p(x); // our precondition
	// ==>?
	assert exists x :: x in s;
	e :| e in s; // "assign-such-that"
	// one could imagine such an assignment:
	// e :| e in s && p(e); // "assign-such-that"
	// but that's naturally not permitted in our course
	// even if Dafny's compiler is magically able to deal with it
	assert e in s; // from the assignment above
	assert exists x :: x in s && p(x); // from our precondition
	if !p(e) {
		assert e in s; // from the assertion ahead of the "if"
		assert !p(e); // the guard
		// on a first attempt in class I forgot to propagate the fact that there exists an element e' such that p(e') is tru
		assert exists x :: x in s && p(x); // from our precondition
		// ==>?
		assert exists x :: x in s-{e} && p(x); // the method's precondition
		assert 0 <= |s-{e}| < |s|; // for termination of the recursion
		ghost var e0 := e; // backup for the call's postcondition
		e := FindElement(s-{e}, p);
		assert e in s-{e0} && p(e);
		// ==>?
		assert e in s && p(e); // propagated from below the "if"
	}
	else { // prove there's no need for the "else" branch:
		assert e in s; // from the assertion ahead of the "if"
		assert p(e); // the negation of the guard
		// ==>
		assert e in s && p(e); // propagated from below the "if"
	}
	assert e in s && p(e); // our postcondition
}

datatype Entry<K,D> = Empty | Full(key: K, datum: D)
type Database<K,D> = seq<Entry<K,D>>

method Find<D>(db: Database<int,D>, k: int) returns (d: D)
	requires exists d': D :: Full(k,d') in db
	ensures Full(k,d) in db
	decreases |db|
{
	match db[0] {
		case Empty =>
			d := Find(db[1..], k);
		case Full(k', d') =>
			if k' == k {
				d := d';
			}
			else {
				d := Find(db[1..], k);
			}
	}
}

// one more version with reference to the "fields" by name
method Find'<D>(db: Database<int,D>, k: int) returns (d: D)
	requires exists d': D :: Full(k,d') in db
	ensures Full(k,d) in db
	decreases |db|
{
	match db[0] {
		case Empty =>
			d := Find(db[1..], k);
		case Full(_, _) =>
			if db[0].key == k {
				d := db[0].datum;
			}
			else {
				d := Find(db[1..], k);
			}
	}
}

// and one final version, without pattern matching
method Find''<D>(db: Database<int,D>, k: int) returns (d: D)
	requires exists d': D :: Full(k,d') in db
	ensures Full(k,d) in db
	decreases |db|
{
	if db[0].Empty? { // the Empty? and Full? are known as discriminators
		d := Find(db[1..], k);
	} else {
		assert db[0].Full?;
		if db[0].key == k {
			d := db[0].datum; // the .key and .datum are known as destructors [in contrast to datatype constructors such as "Empty" or "Full(5, 101)"]
		}
		else {
			d := Find(db[1..], k);
		}
	}
}
