with Types; use Types;

package Insertion_Sort with SPARK_Mode is

   function Is_Sorted (A : Nat_Array; From, To : Index'Base) return Boolean is
     (for all I in From .. To => (for all J in I .. To => A (I) <= A (J)))
   with
     Ghost,
     Pre => From in A'Range and To in A'Range;

   function Is_Sorted (A : Nat_Array) return Boolean is
     (Is_Sorted (A, A'First, A'Last))
       with
         Ghost,
         Pre => A'Length > 0;

   Permutation : Permut_Array(Index) with Ghost;

   function Same_Bounds (Left, Right : Nat_Array) return Boolean is
     (Left'First = Right'First and Left'Last = Right'Last);

   function Is_Perm (Left, Right : Nat_Array) return Boolean is
     (Is_Permutation_Array (Permutation(Left'Range))
       and then
     (for all J in Left'Range => Right (J) = Left (Permutation (J))))
   with
     Ghost,
     Pre => Same_Bounds (Left, Right);


   procedure Insertion_Sort (A : in out Nat_Array)
   with
     Post => A'Length = 0
       or else (Is_Sorted (A) and then Is_Perm (A'Old, A));

end Insertion_Sort;
