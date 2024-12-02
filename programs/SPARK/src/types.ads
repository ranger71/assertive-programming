package Types is -- from Sort_Types in Yannick Moy's implementation of
   -- the Selection Sort and QuickSort of Ch15 in Leino's Program Proofs

   subtype Index is Integer range 1 .. 1000;

   type Nat_Array is array (Index range <>) of Natural;

   type Permut_Array is array (Index range <>) of Index with Ghost;

   function Is_Permutation_Array (Permut : Permut_Array) return Boolean is
     ((for all J in Permut'Range => Permut(J) in Permut'Range)
        and then
      (for all J in Index =>
         (for all K in Index =>
            (if J /= K then Permut (J) /= Permut (K)))))
   with
     Ghost;

end Types;
