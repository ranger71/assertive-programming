package body Linear_Search_Existing_Key with SPARK_Mode is

   function Inv (A : T_Arr; Key : T; I : Index_Type) return Boolean is
     (I in A'Range and then (for some J in A'Range => I <= J and then A (J) = Key))
   with Ghost;

   procedure Lemma_Increment (A : T_Arr; Key : T; I : Index_Type) with Ghost,
     Pre => Inv (A, Key, I) and then A (I) /= Key,
     Post => Inv (A, Key, I + 1) and then I < I + 1
   is
   begin
      null; -- Key is somewhere in the array's suffix starting at I, but not at I,
      -- so it must be in the suffix starting at I+1
   end Lemma_Increment;

   procedure Lemma_Init (A : T_Arr; Key : T) with Ghost,
     Pre => (for some J in A'Range => A (J) = Key),
     Post => Inv (A, Key, A'First)
   is
   begin
      null;
   end Lemma_Init;

   procedure Lemma_Post (A : T_Arr; Key : T; I : Index_Type) with
     Ghost,
     Pre  => Inv (A, Key, I) and then A (I) = Key,
     Post => I in A'Range and then A (I) = Key
   is
   begin
      null;
   end Lemma_Post;

   procedure Search (A : T_Arr; Key : T; I : out Index_Type) is
   begin
     Lemma_Init (A, Key);
     I := A'First;
     pragma Assert (Inv (A, Key, I));
     while A (I) /= Key loop
       Lemma_Increment (A, Key, I);
       I := I + 1;
       pragma Loop_Variant (Increases => I);
       pragma Loop_Invariant (Inv (A, Key, I));
     end loop;
     Lemma_Post (A, Key, I);
   end Search;

end Linear_Search_Existing_Key;
