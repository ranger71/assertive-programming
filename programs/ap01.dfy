/*

Assertive Programming - Spring Semester 2023 - Lecture #1 (8/3/23, online, recorded)

Lectures: Wednesdays 18-20 in classroom 110 building 34
Lecturer: R. Ettinger, ranger@cs.bgu.ac.il, room -104 building 58 (Mathematics), office hours: Wednesdays from 20:10 (after the lecture)

Today: about the course + a first little program

Dafny.org, Ada/SPARK

*/

method {:verify true} Sqrt(n: int) returns (res: int)
	requires n >= 0
	ensures res*res <= n < (res+1)*(res+1)
	// the above is shoerthand for "res*res <= n && n < (res+1)*(res+1)"
{
	res := 0;
	while !(n < (res+1)*(res+1))
		invariant res*res <= n
		decreases n - res*res
	{
		res := res+1;
	}
	assert n < (res+1)*(res+1); // negation of the loop guard
	assert res*res <= n;
}

method Main() {
	//var x := Sqrt(-9); // a precondition might not hold!
	var x := Sqrt(9);
	assert x == 3;
	print "The floor of the non-negative square root of 9 is ", x, "\n";
	x := Sqrt(10);
	assert x == 3;
	print "The floor of the non-negative square root of 10 is ", x, "\n";
}