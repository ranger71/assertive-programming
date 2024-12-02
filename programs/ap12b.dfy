/* inductive datatypes + pattern matching + recursive methods + structural order */
datatype Tree = Empty | Node(nat,Tree,Tree)

method Main() {
	var nt := Node(7,Node(3,Empty,Empty),Empty);
	print "\nThe total sum of all natural numbers in the tree Node(7,Node(3,Empty,Empty),Empty) is ";
	var n := ComputeSumTree(nt);
	print n;
	assert n == 7 + 3;

	n := ComputeSumTreeIter(nt); // compute iteratively this time, instead of recursively
	assert n == 7 + 3;
}

ghost function SumTree(nt: Tree): nat
	decreases nt
{
	match nt {
		case Empty => 0
		case Node(n',nt1,nt2) => n'+SumTree(nt1)+SumTree(nt2)
	}
}

method ComputeSumTree'(nt: Tree) returns (n: nat)
	ensures n == SumTree(nt)
	decreases nt
{
	match nt {
		case Empty =>
			n := 0;
		case Node(n',left,right) =>
			n := n';
			var leftSum := ComputeSumTree(left);
			n := n+leftSum;
			var rightSum := ComputeSumTree(right);
			n := n+rightSum;
	}
}

method ComputeSumTree(nt: Tree) returns (n: nat)
	ensures n == SumTree(nt)
	decreases nt
{
	match nt {
	case Empty =>
		assert nt == Empty;
		// ==>
		assert 0 == SumTree(nt);
		n := 0;
		assert n == SumTree(nt);
	case Node(n',left,right) =>
		assert nt == Node(n',left,right);
		// ==> (by the definition of SumTree for non empty nodes)
		assert n'+SumTree(left)+SumTree(right) == SumTree(nt);
		n := n';
		assert n+SumTree(left)+SumTree(right) == SumTree(nt);

		assert nt == Node(n',left,right);
		// ==> (for termination)
		assert left < nt;
		var leftSum := ComputeSumTree(left);
		assert n+leftSum+SumTree(right) == SumTree(nt);
		n := n+leftSum;
		assert n+SumTree(right) == SumTree(nt); // propagated from below as if the method call was an assignment 

		assert nt == Node(n',left,right); // propagated from above
		// ==> for termination (structural order)
		assert right < nt;

		var rightSum := ComputeSumTree(right); // same as rightSum := SumTree(right);
		assert n+rightSum == SumTree(nt);
		n := n+rightSum;
		assert n == SumTree(nt);
	}
	assert n == SumTree(nt);
}

ghost function SumForest(forest: seq<Tree>): nat
	decreases forest
{
	if forest == [] then 0 else SumTree(forest[0])+SumForest(forest[1..])
}

ghost function ForestSize(forest: seq<Tree>): nat
	decreases forest
{
	if forest == [] then 0 else TreeSize(forest[0])+ForestSize(forest[1..])
}

ghost function TreeSize(nt: Tree): nat
	decreases nt
{
	match nt {
		case Empty => 1 // 0 here would have not been good enough!!!
		case Node(n',nt1,nt2) => 1+TreeSize(nt1)+TreeSize(nt2)
	}
}

method ComputeSumTreeIter(nt: Tree) returns (n: nat) // iteratively, not recursively
	ensures n == SumTree(nt)
{
	var stack := [nt];
	n := 0;
	// the variant in this case is not so trivial...
	while stack != []
		invariant SumTree(nt) == n+SumForest(stack)
		decreases ForestSize(stack)
	{
		ghost var V0 := ForestSize(stack);
		var tree;
		tree, stack := stack[0], stack[1..]; // pop
		match tree {
			case Empty => // skip
			case Node(n',left,right) =>
				stack := [left, right] + stack; // push
				n := n+n';
		}
		// interestingly, Dafny does not see that the variant indeed decreases in each iteration until we add the following assertion
		assert 0 <= ForestSize(stack) < V0;
	}
}
