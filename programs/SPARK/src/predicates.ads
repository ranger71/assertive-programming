with Types; use Types;

package Predicates with
  SPARK_Mode,
  Ghost
is

   function Remove_Last (A : T_Arr) return T_Arr is
     (A (A'First .. A'Last - 1))
   with
     Pre => A'Length > 0;

   function Occ_Def (A : T_Arr; Val : T) return Natural is
     (if A'Length = 0
        then 0
      elsif A (A'Last) = Val
        then Occ_Def (Remove_Last (A), Val) + 1
      else
        Occ_Def (Remove_Last (A), Val))
   with
     Post => Occ_Def'Result <= A'Length;
   pragma Annotate (GNATprove, Terminating, Occ_Def);
   pragma Annotate (GNATprove, False_Positive, "subprogram ""Occ_Def"" might not terminate",
                    "Termination is guaranteed thanks to using Remove_Last");
   function Occ (A : T_Arr; Val : T) return Natural is
     (Occ_Def (A, Val))
   with
     Post => Occ'Result <= A'Length;

   function Multiset_Unchanged (A, B : T_Arr) return Boolean is
      (for all K in T => Occ (A, K) = Occ (B, K))
   with
         Pre => A'Length = B'Length;

   function Is_Set
     (A : T_Arr;
      J : Positive;
      V : T;
      B : T_Arr)
      return Boolean is
     (A'First = B'First and then A'Last = B'Last and then B (J) = V
      and then (for all K in A'Range => (if J /= K then B (K) = A (K)))) with
      Pre => J in A'Range;

   procedure Occ_Set
     (A : T_Arr;
      B : T_Arr;
      J : Positive;
      V : T;
      E : T) with
      Pre  => J in A'Range and then Is_Set (A, J, V, B),
      Post =>
      (if V = A (J) then Occ (B, E) = Occ (A, E)
       elsif V = E then Occ (B, E) = Occ (A, E) + 1
       elsif A (J) = E then Occ (B, E) = Occ (A, E) - 1
             else Occ (B, E) = Occ (A, E));

  function Sorted (A : T_Arr) return Boolean is
    (for all J in A'Range =>
       (for all K in A'First .. J - 1 => A (K) <= A (J)));

end Predicates;
