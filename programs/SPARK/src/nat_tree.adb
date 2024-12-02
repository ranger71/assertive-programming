package body Nat_Tree is

   procedure Compute_Sum_Tree (T : Tree; Sum : out Big_Natural) is
      S0: Big_Natural;
      S1: Big_Natural;
   begin
      -- Sum := Sum_Tree(T); -- error: ghost entity cannot appear in this context
      if T.Kind = Node then
         Compute_Sum_Tree (T.Left.all, S0);
         -- pragma Annotate (GNATprove, False_Positive, "terminating annotation",
         --                  "That version of SPARK does not allow structural variant");
         Compute_Sum_Tree (T.Right.all, S1);
         -- pragma Annotate (GNATprove, False_Positive, "terminating annotation",
         --                  "That version of SPARK does not allow structural variant");
         Sum := T.Value + S0 + S1;
      else
         pragma Assert (T.Kind = Empty);
         Sum := 0;
      end if;
   end Compute_Sum_Tree;   

end Nat_Tree;
