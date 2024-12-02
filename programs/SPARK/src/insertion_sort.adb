package body Insertion_Sort with SPARK_Mode is
   -- initially developed by Joffrey Huguet and Rani Ettinger in 2019, based on
   -- Carroll Morgan's "Programming from Specifications" Chapter 10
   -- and some pre-existing multiset-related ingredients by folks at AdaCore;
   -- updated May 2023 with ingredients from Yannick Moy's implementation
   -- of Leino's Program Proofs Chapter 15 (Selection Sort and Quicksort)

   function Inv_1 (A, A_Entry : Nat_Array; I : Integer) return Boolean is
     (A'Length > 0 and then I in A'Range and then
      Is_Sorted (A (A'First .. I)) and then
      Same_Bounds (A_Entry, A) and then Is_Perm (A_Entry, A))
   with Ghost;

   function Is_Sorted_Except_At (A : Nat_Array; K : Index) return Boolean is
     (for all I in A'Range =>
        (for all J in A'First .. I - 1 =>
           (if I /= K and then J /= K
            then A (J) <= A (I))))
   with Ghost;

   function Inv_2 (A, A_Entry : Nat_Array; I, J : Index) return Boolean is
     (A'Length > 1 and then Same_Bounds (A_Entry, A) and then Is_Perm (A_Entry, A)
      and then I in A'First .. A'Last-1
      and then J in A'First .. I + 1
      and then Is_Sorted_Except_At (A (A'First .. I + 1), J)
      and then (for all K in J + 1 .. I + 1 => A (J) < A (K)))
    with Ghost;

   function Insertion_Guard (A, A_Entry: Nat_Array; I, J : Index) return Boolean is
     (A'First < J and then A (J - 1) > A (J))
       with
         Pre => Inv_2 (A, A_Entry, I, J);

   procedure Lemma_Insert_Init (A, A_Entry : Nat_Array; I : Index) with
     Ghost,
     Pre  => Inv_1 (A, A_Entry, I) and then I /= A'Last,
     Post => Inv_2 (A, A_Entry, I, I + 1)
   is
      --  j, K : Index;
      --  A_Prefix : constant Nat_Array := A (A'First .. I + 1);
   begin
      --  -- from the precondition we know:
      --  pragma Assert (A'Length > 0);
      --  pragma Assert (I in A'Range);
      --  pragma Assert (Is_Sorted (A (A'First .. I)));
      --  pragma Assert (Same_Bounds (A_Entry, A));
      --  pragma Assert (Is_Perm (A_Entry, A));
      --  pragma Assert (I /= A'Last);
      --  -- and for the postcondition we need to know:
      --  j := I + 1;
      --  pragma Assert (A'Length > 1);
      --  pragma Assert (Same_Bounds (A_Entry, A));
      --  pragma Assert (Is_Perm (A_Entry, A));
      --  pragma Assert (I in A'First .. A'Last-1);
      --  pragma Assert (J in A'First .. I + 1);
      --  pragma Assert (for all K in J + 1 .. I + 1 => A (J) < A (K));
      --  -- and only one does not verify at first:
      --  -- pragma Assert (Is_Sorted_Except_At (A (A'First .. I + 1), J));
      --  -- so let's break it down into its ingredients:
      --  K := J;
      --  pragma Assert ((for all I in A_Prefix'Range =>
      --    (for all J in A_Prefix'First .. I - 1 =>
      --       (if I /= K and then J /= K
      --        then A_Prefix (J) <= A_Prefix (I)))));
      null;
   end Lemma_Insert_Init;

   --procedure Prove_Inv2 (J : Index) with
   --  Ghost,
   --  Pre  => Inv_2 (A, A_Entry, I, J) and then Insertion_Guard (J),
   --  Post => Inv_2 (A'Update (J - 1 => A (J), J => A (J - 1)), I, J - 1)
   --is
   --begin
   --   null;
   --end Prove_Inv2;

   procedure Stronger_Postcondition_2 (A, A_Entry : Nat_Array; I, J : Index) with
      Ghost,
      Pre  => Inv_2 (A, A_Entry, I, J) and then (not Insertion_Guard (A, A_Entry, I, J)),
      Post => Inv_1 (A, A_Entry, I + 1)
   is
   begin
      null;
   end Stronger_Postcondition_2;

   ----------------------
   --  Insertion_Sort  --
   ----------------------

   procedure Insertion_Sort (A : in out Nat_Array) is
      -- [As in Moy's Quicksort] Record entry value of A for use in calls to Is_Perm property
      A_Entry : constant Nat_Array := A with Ghost;
      I : Index;

      procedure Lemma_Insertion_Sort_Init (A : Nat_Array) with
        Ghost,
        Pre => A'Length > 0 and then A = A_Entry
         and then Same_Bounds (A_Entry, A) and then Is_Perm (A_Entry, A),
        Post => Inv_1 (A, A_Entry, A'First)
      is
      begin
         null;
      end Lemma_Insertion_Sort_Init;

      procedure Stronger_Postcondition_1 (A : Nat_Array; I : Index) with
        Ghost,
        Pre  => Inv_1 (A, A_Entry, I) and then I = A'Last,
        Post => A'Length = 0
        or else (Is_Sorted (A) and then Is_Perm (A_Entry, A))
      is
      begin
         null;
      end Stronger_Postcondition_1;

      -- Swap + Permutation borrowed from Yannick Moy's implementation of
      -- the Selection Sort and QuickSort of Ch15 in Leino's Program Proofs

      -- Swap the A of A (X) and A (Y).
      -- We could also remove the contract and let it be inlined for proof.
      procedure Swap (A : in out Nat_Array; X, Y : Index)
        with
          Pre  => X in A'Range and Y in A'Range,
        Post => A = (A'Old with delta
                       X => A'Old (Y),
                     Y => A'Old (X))
        and then Permutation = (Permutation'Old with delta
                                  X => Permutation'Old (Y),
                                Y => Permutation'Old (X))
      is
         Temp       : Integer;
         Temp_Index : Index with Ghost;
      begin
         Temp  := A (X);
         A (X) := A (Y);
         A (Y) := Temp;

         Temp_Index := Permutation (X);
         Permutation (X) := Permutation (Y);
         Permutation (Y) := Temp_Index;
      end Swap;

      procedure Swap_Left (A : in out Nat_Array; I, J : Index) with
        Pre  => Inv_2 (A, A_Entry, I, J) and then Insertion_Guard (A, A_Entry, I, J),
        Post => Inv_2 (A, A_Entry, I, J - 1)
      is
      begin
         Swap (A, J - 1, J);
      end Swap_Left;

      --------------
      --  Insert  --
      --------------

      procedure Insert (A : in out Nat_Array; I : Index) with
        Pre  => Inv_1 (A, A_Entry, I) and then I /= A'Last,
        Post => Inv_1 (A, A_Entry, I + 1)
      is
      J : Index;

      begin
         Lemma_Insert_Init (A, A_Entry, I);
         J := I + 1;
         while A'First < J and then A (J - 1) > A (J) loop
            pragma Loop_Invariant (Inv_2 (A, A_Entry, I, J));
            pragma Loop_Variant (Decreases => J);

            Swap_Left (A, I, J);
            J := J - 1;
         end loop;
         Stronger_Postcondition_2 (A, A_Entry, I, J);
      end Insert;

   begin
      if A'Length > 0 then
         Permutation := (for K in Index => K);
         Lemma_Insertion_Sort_Init (A);
         I := A'First;
         while I /= A'Last loop
            pragma Loop_Invariant (Inv_1 (A, A_Entry, I));
            pragma Loop_Variant (Increases => I);

            Insert (A, I);
            I := I + 1;
         end loop;
         Stronger_Postcondition_1 (A, I);
      end if;
   end Insertion_Sort;

end Insertion_Sort;
