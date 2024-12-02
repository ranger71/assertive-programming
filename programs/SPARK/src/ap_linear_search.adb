package body AP_Linear_Search with SPARK_Mode is

   function Inv (A : T_Arr; Key : T; I : Index_Type) return Boolean is
     (A'Length > 0 and then
      I in A'Range and then
      ((A (I) = Key) = (for some J in A'First .. I => A (J) = Key)))
   with Ghost;

   function Guard (A : T_Arr; Key : T; I : Index_Type) return Boolean is
     (A (I) /= Key and then I < A'Last)
   with Pre => Inv (A, Key, I);

   procedure Lemma_Increment (A : T_Arr; Key : T; I : Index_Type) with Ghost,
     Pre => Inv (A, Key, I) and then Guard (A, Key, I),
     Post => Inv (A, Key, I + 1) and then I < I + 1
   is
   begin
      null;
   end Lemma_Increment;

   procedure Lemma_Init (A : T_Arr; Key : T) with
     Ghost,
     Pre => A'Length > 0,
     Post => Inv (A, Key, A'First)
   is
   begin
      null;
   end Lemma_Init;

   function Result_Expression (A : T_Arr; Key : T; I : Index_Type) return Maybe_Index_Type
   is (if A (I) = Key then (Found => True, Index => I) else (Found => False))
   with Pre => I in A'Range;

   procedure Lemma_Post (A : T_Arr; Key : T; I : Index_Type) with
     Ghost,
     Pre  => Inv (A, Key, I) and then not Guard (A, Key, I),
     Post => I in A'Range and then Search_Post (A, Key, Result_Expression (A, Key, I))
   is
   begin
      -- this is proved by SPARK; still, for the reader:
      if A (I) = Key then
         pragma Assert (for some J in A'Range => A (J) = Key);
      else
         pragma Assert (I = A'Last); -- from the negation of the guard
         pragma Assert (not (for some J in A'First .. I => A (J) = Key));
         pragma Assert (not (for some J in A'Range => A (J) = Key));
      end if;
   end Lemma_Post;

   procedure Lemma_Empty_Array (A : T_Arr; Key : T)
     with Ghost,
     Pre => A'Length = 0,
     Post => Search_Post (A, Key, (Found => False))
   is
   begin
      null;
   end Lemma_Empty_Array;

   function Search (A : T_Arr; Key : T) return Maybe_Index_Type is
      Result : Maybe_Index_Type;
      I : Index_Type;
   begin
      if A'Length = 0 then
         Lemma_Empty_Array (A, Key);
         Result := (Found => False);
      else
         Lemma_Init (A, Key);
         I := A'First;
         pragma Assert (Inv (A, Key, I));
         while A (I) /= Key and then I < A'Last loop -- Guard (A, Key, I)
            Lemma_Increment (A, Key, I);
            I := I + 1;
            pragma Loop_Variant (Increases => I);
            pragma Loop_Invariant (Inv (A, Key, I));
         end loop;
         Lemma_Post (A, Key, I);
         Result := Result_Expression (A, Key, I);
      end if;
      return Result;
   end Search;

end AP_Linear_Search;
