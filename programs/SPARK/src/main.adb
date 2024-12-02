with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with NAT_TREE; use NAT_TREE;

procedure Main is
   T: constant Tree := Tree'(Kind => Empty);
   S: Big_Natural;
begin
   --  Insert code here.
   Compute_Sum_Tree (T, S);
   pragma Assert (S = 0);
end Main;
