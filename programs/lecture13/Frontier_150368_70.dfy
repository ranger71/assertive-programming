datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)
/// 70 [no lemmas or evident familiarity with proof obligations; inefficient extra (should be ghost) sequence]
class IO<T> {
	var alpha: seq<T>, omega: seq<T>;

	method Input() returns (x: T)
		requires !EOF() // alpha != []
		modifies this
		ensures omega == old(omega)
		ensures old(alpha) == [x] + alpha
	{
		x, alpha := alpha[0], alpha[1..];
	}

	method Output(x: T)
		modifies this
		ensures alpha == old(alpha)
		ensures omega == old(omega) + [x]
	{
		omega := omega + [x];
	}

	method Rewrite()
		modifies this
		ensures omega == []
		ensures alpha == old(alpha)
	{
		omega := [];
	}

	predicate method EOF() reads this { alpha == [] }

}

method Main()
{
	var tree: BT<int>;
	tree := Tip(1);
	var io: IO<int>;
	io := new IO<int>;
	FrontierIter(tree, io);
	print io.omega;

	io.Rewrite();
	tree := Node(tree, Tip(2));
	FrontierIter(tree, io);
	print io.omega;
}

function Frontier<T>(tree: BT<T>): seq<T>
{
	match tree {
		case Tip(n) => [n]
		case Node(left, right) => Frontier(left) + Frontier(right)
	}
}

function Frontiers<T>(trees: seq<BT<T>>): seq<T>
{
	if trees == [] then [] else Frontier(trees[0]) + Frontiers(trees[1..])
}

// TODO: implement iteratively (with a loop),
// updating the value of "io.omega" through calls to "io.Output" for each "tip" of the tree;
// document each proof obligation, as we've learned, with assertion propagation and a lemma
method FrontierIter<T>(tree: BT<T>, io: IO<T>)
	modifies io
	ensures io.omega == old(io.omega) + Frontier(tree)
	{
	var stack := [tree];
	var k:seq<T> := []; /// ghost!
	assert io.omega == old(io.omega) + k;
	while stack != [] 
		invariant Frontier(tree) == k + Frontiers(stack) 
		invariant io.omega  == old(io.omega) + k  
		decreases TreesNodeNum(stack); //the number of total nodes in the stack decreases
	{
		assert stack != [];
		ghost var V0 := TreesNodeNum(stack);
		var temptree := stack[0];    //get first var is stack
		stack := stack[1..];         //pop
	    match temptree{
			case Tip(n) =>
				 k :=  k + [n] ;
				 io.Output(n);
			case Node(tree1,tree2) =>
				stack:=[tree1,tree2] + stack;  
		}
		assert 0 <= TreesNodeNum(stack) < V0; //proof the while stops
		assert Frontier(tree) == k + Frontiers(stack);
		assert io.omega  == old(io.omega) + k;
	}
	assert Frontier(tree) == k + Frontiers(stack) ;
	assert stack == [];
	assert Frontier(tree) == k;
	assert io.omega  == old(io.omega) + k ;
	assert io.omega  == old(io.omega) + Frontier(tree);  
}

function TreeNodeNum<T>(tree: BT<T>) : nat
{
	match tree {
		case Tip(n) => 1
		case Node(left, right) => 1 + TreeNodeNum(left) + TreeNodeNum(right)
	}
}

function TreesNodeNum<T>(trees: seq<BT<T>>) : nat
{
	if trees == [] then 0 else TreeNodeNum(trees[0]) + TreesNodeNum(trees[1..])
}