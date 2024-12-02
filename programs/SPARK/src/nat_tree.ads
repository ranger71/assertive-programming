with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Containers.Functional_Maps; use Ada.Containers;

package Nat_Tree is

   type Tree_Kind is (Empty, Node);
   type Tree;
   type Tree_Acc is not null access constant Tree;
   type Tree (Kind : Tree_Kind) is record
      case Kind is
         when Node  =>
            Value : Big_Natural;
            Left  : Tree_Acc;
            Right : Tree_Acc;
         when Empty =>
            null;
      end case;
   end record;
   
--   function New_Tree (t : Tree) return Tree_Acc is
--     (new Tree'(t))
--   with
--     Annotate => (GNATprove, Intentional, "memory leak",
--                  "allocation of access-to-constant is not reclaimed");

   function Sum_Tree (T : Tree) return Big_Natural is
     (case T.Kind is
         when Empty => To_Big_Integer (0),
         when Node  =>
           (declare
              S0 : constant Big_Natural := Sum_Tree (T.Left.all);
              S1 : constant Big_Natural := Sum_Tree (T.Right.all);
            begin
              (T.Value + S0 + S1)))
      with
      Ghost,
      Annotate => (GNATprove, Terminating),
      Annotate => (GNATprove, False_Positive, "terminating annotation",
                   "That version of SPARK does not allow structural variant");

   
   procedure Compute_Sum_Tree (T : Tree; Sum : out Big_Natural)
     with
       Post => Sum = Sum_Tree(T);
   
end Nat_Tree;
