datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)
/// 95 [missing termination propagation+proof]
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
		var stack := [tree];		//Simulate stack using sequence
		LemmaBeforeWhile(tree, stack, io,old(io.omega));
		while stack!=[]
			invariant old(io.omega) + Frontier(tree) ==  io.omega + Frontiers(stack) //We describe that what we calculate will be what we ensures plus a gap
			decreases ForestSize(stack)
			{
				//Sanity for guard and invariant
				assert stack!=[];
				assert old(io.omega) + Frontier(tree) ==  io.omega + Frontiers(stack);

				ghost var V0 := ForestSize(stack); 							//Saving the alleged decreasing value to proff its actually decreases
				var subtree:=tree; /// ???
				LemmaSanityWhile(tree, subtree ,stack, io,old(io.omega));
				assert old(io.omega) + Frontier(tree) ==  io.omega + Frontier(stack[0]) + Frontiers(stack[1..]);
				subtree, stack := stack[0], stack[1..];						//Simulate pop operation and stack update
				assert old(io.omega) + Frontier(tree) ==  io.omega + Frontier(subtree) + Frontiers(stack);

				match subtree{
					case Tip(t) =>
						assert subtree==Tip(t);																		//Propagted from up
						assert old(io.omega) + Frontier(tree) ==  io.omega + Frontier(subtree) + Frontiers(stack);	//Propagted from up
						LemmaTip(tree, subtree ,stack, io,old(io.omega),t);
						//==>
						assert old(io.omega) + Frontier(tree) ==  io.omega + [t] + Frontiers(stack); 				//Propegated from below
						io.Output(t);																				//We need to update IO because we did reach a Tip.
						assert old(io.omega) + Frontier(tree) ==  io.omega + Frontiers(stack); 						//Invariant

					case Node(left, right) =>
						assert subtree==Node(left, right);															//Propagted from up
						assert old(io.omega) + Frontier(tree) ==  io.omega + Frontier(subtree) + Frontiers(stack); 	//Propagted from up
						LemmaNode(tree, subtree ,stack, io,old(io.omega),left,right);
						//==>
						assert old(io.omega) + Frontier(tree) ==  io.omega + Frontiers([left,right]+stack); 	//Propegated from below
						stack:= [left,right]+stack;																//Simulation push of the two sibilings (DFS)
					 																							//We dont need to update IO because we did not reach a Tip.
						assert old(io.omega) + Frontier(tree) ==  io.omega + Frontiers(stack); 					// Invariant
				}
				assert old(io.omega) + Frontier(tree) ==  io.omega + Frontiers(stack); 							// Invariant
				assert 0 <= ForestSize(stack) < V0;																// Decreases /// missing termination propagation+proof
			}
		assert !(stack!=[]);																					// Neg on guard
		assert old(io.omega) + Frontier(tree) ==  io.omega + Frontiers(stack); 									// Invariant
		LemmaEnd(tree, stack, io,old(io.omega));
		//==>
		assert io.omega == old(io.omega) + Frontier(tree);														// Post condition we what to ensure
	}


//Recursive forest size calculation using pattern matching as we saw at class
function ForestSize<T>(forest: seq<BT<T>>): nat
	decreases forest
	{
		if forest == [] then 0 else TreeSize(forest[0])+ForestSize(forest[1..])
	}

//Recursive tree size calculation using pattern matching as we saw at class
function TreeSize<T>(tree: BT<T>): nat
	decreases tree
	{
		match tree{
			case Tip(t) => 1
			case Node(left, right) => 1 + TreeSize(left) + TreeSize(right)
		}
	}

lemma {:verify true} LemmaTip<T>(tree: BT<T>,subtree: BT<T>, stack: seq<BT<T>>, io: IO<T>, oldOmega: seq<T>, t:T)
	requires subtree==Tip(t)												//Match Tip guard
	requires oldOmega + Frontier(tree) ==  io.omega + Frontier(subtree) + Frontiers(stack);	//Propogation of inv from up
	ensures oldOmega + Frontier(tree) ==  io.omega + [t] + Frontiers(stack)
	{}

lemma {:verify true} LemmaNode<T>(tree: BT<T>,subtree: BT<T>, stack: seq<BT<T>>, io: IO<T>, oldOmega: seq<T>, left: BT<T>, right: BT<T>)
	requires subtree==Node(left, right)																//Propagted from up
	requires oldOmega + Frontier(tree) ==  io.omega + Frontier(subtree) + Frontiers(stack) 			//Propagted from up
	ensures oldOmega + Frontier(tree) ==  io.omega + Frontiers([left,right]+stack)
	{}

lemma {:verify true} LemmaBeforeWhile<T>(tree: BT<T>, stack: seq<BT<T>>, io: IO<T>, oldOmega: seq<T>)
	requires stack == [tree]
	requires oldOmega == io.omega
	ensures stack != []													//Guard
	ensures oldOmega + Frontier(tree) ==  io.omega + Frontiers(stack)	//Inv
	{}

lemma {:verify true} LemmaSanityWhile<T>(tree: BT<T>,subtree: BT<T>, stack: seq<BT<T>>, io: IO<T>, oldOmega: seq<T>)
	requires stack!=[]														//Guard
	requires oldOmega + Frontier(tree) ==  io.omega + Frontiers(stack)		//Inv
	requires subtree==tree
	ensures oldOmega + Frontier(tree) ==  io.omega + Frontier(stack[0]) + Frontiers(stack[1..])
	{}

lemma {:verify true} LemmaEnd<T>(tree: BT<T>, stack: seq<BT<T>>, io: IO<T>, oldOmega: seq<T>)
	requires !(stack!=[])												// Neg on guard
	requires oldOmega + Frontier(tree) ==  io.omega + Frontiers(stack)	// Inv
	ensures io.omega == oldOmega + Frontier(tree)	//Post conditions
	{}