datatype BT<T> = Tip(T) | Node(BT<T>, BT<T>)
/// 40 [minimal annotation to ensure verification]
class IO<T> {
    var alpha: seq<T>, omega: seq<T>;

    method Input() returns (x: T)
        requires !EOF() //alpha != []
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

function Size<T>(tree: BT<T>): nat
{
    match tree
        case Tip(_) => 1
        case Node(l, r) => Size(l) + Size(r) + 1
}

function SizeInTotal<T>(trees: seq<BT<T>>): nat
{
    if [] == trees then 0 else SizeInTotal(trees[1..]) + Size(trees[0]) 
}

method FrontierIter<T>(tree: BT<T>, io: IO<T>)
    modifies io
    ensures io.omega == old(io.omega) + Frontier(tree)
{
    var curr: BT<T>;
    var trees: seq<BT<T>>;

    trees := [tree];

    while trees != []
        invariant io.omega + Frontiers(trees) == old(io.omega) + Frontier(tree)
        decreases SizeInTotal(trees)
    {
        ghost var former_trees := trees;
        assert old(io.omega) + Frontier(tree) == io.omega + Frontiers(former_trees) ;
        curr:= trees[0];
        trees := trees[1..];
        match curr {
            case Tip(x) => io.Output(x);
            case Node(l, r) => {
                trees := [l, r] + trees;
                assert SizeInTotal(trees) ==  SizeInTotal(trees[2..]) +Size(l) + (Size(r) );
                calc {
                    Frontiers(trees);
                    == Frontiers(former_trees);
                    == Frontier(l) + (Frontier(r) + Frontiers(trees[2..]));

                }
            }
        }
    }
}