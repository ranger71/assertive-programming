/*
Following SPARK's
    https://github.com/AdaCore/spark2014/blob/master/testsuite/gnatprove/tests/red_black_trees/tree_model.ads
    https://github.com/AdaCore/spark2014/blob/master/testsuite/gnatprove/tests/red_black_trees/binary_trees.ads
    https://github.com/AdaCore/spark2014/blob/master/testsuite/gnatprove/tests/red_black_trees/binary_trees.adb

Which has acted as the basic data structure for the implementation of binary-search trees and in particular
balanced BSTs: red-black trees. In case you're interested in that original context, you're welcome to have a look
at the original paper, presented at NASA Formal Methods symposium 2017 by AdaCore's Claire Dross and Yannick Moy:

https://blog.adacore.com/research-corner-auto-active-verification-in-spark
https://blog.adacore.com/uploads/Auto-Active-Proof-of-Red-Black-Trees-in-SPARK.pdf

*/

module Tree_Model {
    const Max: int := 100
    const Empty: int := -1
    type Index_Type = x: int | Empty < x < Max
    type Extended_Index_Type = x: int | Empty <= x < Max
    type Extended_Index_Type_With_Max = x: int | Empty < x <= Max

    const All_Indexes := set I: Index_Type | true // meaning Empty < I < Max

    lemma Max_Indexes()
        ensures |All_Indexes| == Max
    {
        var I := 0;
        var Smaller, Larger := {}, All_Indexes;
        while I < Max
            invariant I <= Max
            invariant Smaller == set x | x in All_Indexes && 0 <= x < I
            invariant Larger == set x | x in All_Indexes && I <= x < Max
            invariant |Smaller| == I
            invariant Smaller + Larger == All_Indexes
            decreases Max - I
        {
            Smaller, Larger := Smaller + {I}, Larger - {I};
            I := I + 1;
        }
    }
    
    datatype Position_Type = Left | Right | Top
    type Direction = d: Position_Type | d != Top witness Left
    type D_Seq = q: seq<Direction> | |q| <= Max // sequence of directions modelling a path from the root of the tree to a node in the tree

    /*
        Type used to model the path from the root of a tree to a given node, which may or not be in the tree:
        - if a node is in the tree, the corresponding path will have K == true,
        and A will denote the path from the root to this node.
        - if a node is not in the tree, the corresponding path will have K == false and A will be empty.
    */
    datatype Path_Type = MaybePath(A: D_Seq, K: bool)

    ghost predicate Is_Concat(Q: D_Seq, V: D_Seq, P: D_Seq) { P == Q + V }

    // Type used to model the set of paths from the root of a tree to all nodes.
    // This is useful to reason about reachability properties over a tree.
    type Model_Type = q: seq<Path_Type> | |q| == Max witness *

    predicate Is_Add(S1: D_Seq, D: Direction, S2: D_Seq) { S2 == S1 + [D] }

    type Value_Set = set<nat>
}

// end of definitions from tree_model.ads, start of definitions from binary_trees.ads

/*
    Here's an implementation of binary trees, modeled using indexes inside an array.
    To avoid multiple copies, related trees are stored together forming a forest.
*/
module Binary_Trees {
    import opened Tree_Model

    type Cell = (Extended_Index_Type, Extended_Index_Type, Extended_Index_Type, Position_Type)
    function Left_Child(C: Cell): Extended_Index_Type { C.0 }
    function Right_Child(C: Cell): Extended_Index_Type { C.1 }
    function Parent(C: Cell): Extended_Index_Type { C.2 }
    function Position(C: Cell): Position_Type { C.3 }

    type Cell_Array = a: array<Cell> | a.Length == Max witness *
    
    // Component S gives the size of the forest. Only the cells up to index S belong to the forest. Cells after index S are free.
    type Forest = (Extended_Index_Type_With_Max, Cell_Array)
    function S(F: Forest): Extended_Index_Type_With_Max { F.0 }
    function C(F: Forest): Cell_Array { F.1 }

    ghost predicate Tree_Structure(F: Forest)
        reads C(F)
    {
        // Cells that are not allocated yet have default values
        (forall I: Index_Type :: S(F) < I < Max ==> C(F)[I] == (Empty, Empty, Empty, Top)) &&
        
        // Parent and children of all cells are allocated or empty
        (forall I: Index_Type :: Empty <= Parent(C(F)[I]) < S(F)) && 
        (forall I: Index_Type :: Empty <= Left_Child(C(F)[I]) < S(F)) && 
        (forall I: Index_Type :: Empty <= Right_Child(C(F)[I]) < S(F)) &&
        
        // If a cell is the root of a tree (position Top) it has no parent
        (forall I: Index_Type :: Position(C(F)[I]) == Top ==> Parent(C(F)[I]) == Empty) && 

        // If a cell I has a left child, then its left child has position Left and parent I
        (forall I: Index_Type :: Left_Child(C(F)[I]) != Empty ==> 
            Position(C(F)[Left_Child(C(F)[I])]) == Left && Parent(C(F)[Left_Child(C(F)[I])]) == I) &&

        // If a cell I has a right child, then its right child has position Right and parent I
        (forall I: Index_Type :: Right_Child(C(F)[I]) != Empty ==>
            Position(C(F)[Right_Child(C(F)[I])]) == Left && Parent(C(F)[Right_Child(C(F)[I])]) == I) && /// FIXME: Alex D. found a typo here - should be "Right"
        
        // If a cell is a child (position Left or Right), then it is the child of its parent
        (forall I: Index_Type :: Parent(C(F)[I]) != Empty && Position(C(F)[I]) == Left ==> Left_Child(C(F)[Parent(C(F)[I])]) == I) &&
        (forall I: Index_Type :: Parent(C(F)[I]) != Empty && Position(C(F)[I]) == Right ==> Right_Child(C(F)[Parent(C(F)[I])]) == I)
    }

    ghost predicate Valid_Root(F: Forest, I: Index_Type)
        reads C(F)
    {
        I < S(F) && Position(C(F)[I]) == Top
    }

    ghost function Size(F: Forest): Extended_Index_Type_With_Max {
        S(F)
    }

    ghost function Parent_Of(F: Forest, I: Index_Type): Extended_Index_Type
        reads C(F)
    {
        Parent(C(F)[I])
    }

    ghost function Position_Of(F: Forest, I: Index_Type): Position_Type
        requires Tree_Structure(F)
        reads C(F)
    {
        Position(C(F)[I])
    }

    ghost function Peek(F: Forest, I: Index_Type, D: Direction): Extended_Index_Type
        reads C(F)
    {
        if D == Left then Left_Child(C(F)[I]) else Right_Child(C(F)[I])
    }

    ghost predicate In_Tree(F: Forest, Root: Index_Type, I: Index_Type)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
    {
        if I == Root then
            true
        else if I >= Size(F) then
            false
        else
            In_Tree_Rec(F, Root, Parent_Of(F, I), {I})
    }

    ghost predicate In_Tree_Rec(F: Forest, Root: Index_Type, I: Extended_Index_Type, Visited: set<Index_Type>)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
        decreases All_Indexes - Visited
    {
        if I == Root then
            true
        else if I == Empty || I in Visited then
            false
        else
            In_Tree_Rec(F, Root, Parent_Of(F, I), Visited + {I})
    }

    ghost function Path_From_Root(F: Forest, Root: Index_Type, I: Index_Type): D_Seq
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        reads C(F)
    {
        Path_From_Root_Rec(F, Root, I, {})
    }

    // each node in the forest is a member of one rooted-tree:
    // the node is either the root of its own tree or its parent is a member of the same tree
    lemma {:verify false} Parent_In_Same_Tree(F: Forest, Root: Index_Type, I: Index_Type)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        ensures I == Root || In_Tree(F, Root, Parent_Of(F, I))
    {}

    lemma {:verify false} Lemma_Path_Length(F: Forest, Root: Index_Type, I: Index_Type, Visited: set<Index_Type>, Path: D_Seq)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        requires I !in Visited
        requires Visited < All_Indexes
        requires Path == Path_From_Root_Rec(F, Root, I, Visited)
        ensures |Path| < |All_Indexes - Visited|
        decreases All_Indexes - Visited
    {}
    
    ghost function Path_From_Root_Rec(F: Forest, Root: Index_Type, I: Index_Type, Visited: set<Index_Type>): D_Seq
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        requires I !in Visited
        requires Visited < All_Indexes
        reads C(F)
        decreases All_Indexes - Visited
    {
        if I == Root then
            []
        else if Parent_Of(F, I) !in Visited then
            assert In_Tree(F, Root, Parent_Of(F, I)) by { Parent_In_Same_Tree(F, Root, I); }
            assert I in All_Indexes - Visited;
            var Path_To_Parent: D_Seq := Path_From_Root_Rec(F, Root, Parent_Of(F, I), Visited + {I});
            assert |Path_To_Parent| < |All_Indexes - (Visited + {I})| by {
                Lemma_Path_Length(F, Root, Parent_Of(F, I), Visited + {I}, Path_To_Parent);
            }
            assert |Path_To_Parent| + 1 < |All_Indexes - Visited| <= |All_Indexes| == Max by { Max_Indexes(); }
            assert Position_Of(F, I) == Left || Position_Of(F, I) == Right;
            var res := Path_To_Parent + [Position_Of(F, I)];
            assert |res| < |All_Indexes - Visited|;
            res
        else
            [] // should never reach here thanks to the tree having no cycles
    }

    lemma {:verify false} Lemma_Model_Length(F: Forest, Root: Index_Type, I: Index_Type, Model: seq<Path_Type>)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires Model == Partial_Model_Rec(F, Root, Max - 1)
        ensures |Model| == Max
    {}

    /*
    The model of a tree in the forest is an array representing the path
    from the root leading to each node in the binary tree if any.
    */
    ghost function Model(F: Forest, Root: Index_Type): Model_Type
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
    {
        var res := Partial_Model_Rec(F, Root, Max - 1);
        assert |res| == Max by { Lemma_Model_Length(F, Root, Max - 1, res); }
        res
    }

    ghost function Partial_Model_Rec(F: Forest, Root: Index_Type, I: Index_Type): seq<Path_Type>
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
        decreases I
    {
        var Path_To_I :=
            if In_Tree(F, Root, I) then
                MaybePath(Path_From_Root(F, Root, I), true)
            else
                MaybePath([], false);
        if I == 0 then
            [Path_To_I]
        else
            Partial_Model_Rec(F, Root, I - 1) + [Path_To_I]
    }

    /*
    
    A method to extract the subtree starting at position D after I in the tree rooted at Root in a separate tree and store its root into V.

    Goal: Implement the method in Dafny, following (as closely as you can) the SPARK code (given below in a comment + reference to the original
    open-source online version), with the necessary modifications.

    Full verification is NOT expected in this case. Document the proof obligations for verification of this method using assertions and lemmas
    as we have learned, and try to prove correctness of some of the lammas (as much as you can).
    
    - As there are many not-too-trivial properties to consider, the main challenge in this exercise 
      is to try an understand the definitions, the properties, and the data structure, and then try to argue
      for the correctness of the code
    - Wherever Dafny takes too long to verify correctness ("timing out" after a short attempt), don't worry about it;
      instead, in such cases, feel free to try and document in words, shortly, for as many properties as you can,
      what makes them correct. A sign of success will be if you managed to write the expected code correctly
      and give me some convincing signs that you've managed to comprehend the details of the data structure
      along with its invariants (as defined in the Tree_Structure ghost predicate)
    */
    method {:verify false} Extract(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, ghost F_Old: Forest) returns (V: Extended_Index_Type)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root) && Model(F, Root)[I].K
        requires C(F) != C(F_Old) // the backup forest references ("points") to a different array, one that will NOT be modified
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old) // and it is indeed a backup of the given forest, holding equal contents on entry
        modifies C(F) // in contrast to C(F_Old) which is a different array (as mentioned above)
        ensures Tree_Structure(F)
        // Root is still the root of a tree
        ensures Valid_Root(F, Root)
        // V was the child D of I, which is now Empty
        ensures V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty
        // Except for V, the value of parent link is preserved
        ensures forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J)
        // Except for V, the value of position is preserved for nodes which have a parent
        ensures forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J)
        // Except at I for child D, all other children are preserved
        ensures forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E)
        // Except for I and V (which was not a root node anyway), all root nodes are preserved
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T);
        // All other trees in the forest are preserved
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T)
        // V is either Empty or a new root
        ensures V != Empty ==> Valid_Root(F, V)
        // Nodes previously in the tree rooted at Root either remain nodes in
        // the tree rooted at Root, or for those nodes which have V on their
        // path, become nodes in the tree rooted at V
        ensures forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
            if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K
        // Nodes in the tree rooted at Root were previously in the tree rooted at Root
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K
        // Nodes in the tree rooted at V were previously in the tree rooted at Root
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K
        // Paths are preserved for nodes in the tree rooted at Root
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A
        // The path for nodes in the tree rooted at V is obtained by subtracting
        // the path from Root to V from the path from Root to the node
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
            Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A)
    {
        /*
        The SPARK code (lines 630-647 in https://github.com/AdaCore/spark2014/blob/master/testsuite/gnatprove/tests/red_black_trees/binary_trees.adb)
        (where Prove_Post is a local lemma that takes no parameters since all prameters are in its scope)

        V := (if D = Left then F.C (I).Left else F.C (I).Right);

        if V /= Empty then
            if D = Left then
                F.C (I).Left := Empty;
            else
                F.C (I).Right := Empty;
            end if;
            pragma Assert (F.C (V).Parent = I);
            F.C (V).Position := Top;
            F.C (V).Parent := Empty;
        end if;

        pragma Assert (Tree_Structure (F));

        if V /= Empty then
            Prove_Post;
        end if;

        */
    }
}
