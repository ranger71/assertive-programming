package body CCPR_Linear_Search with SPARK_Mode is

   function Inv (A : T_Arr; Key : T; I : Index_Type) return Boolean is
     (A'Length > 0 and then
      I in A'Range and then
      ((A (I) = Key) = (for some J in A'First .. I => A (J) = Key)))
   with Ghost;

   function Guard (A : T_Arr; Key : T; I : Index_Type) return Boolean is
     (A (I) /= Key and then I < A'Last)
   with Pre => Inv (A, Key, I);

   procedure Lemma_4 (A : T_Arr; Key : T; I : Index_Type) with Ghost,
     Pre => Inv (A, Key, I) and then Guard (A, Key, I),
     Post => Inv (A, Key, I + 1) and then I + 1 > I
   is
   begin
      null;
   end Lemma_4;

   procedure Search_4 (A : T_Arr; Key : T; I : in out Index_Type) with
     Pre => Inv (A, Key, I) and then Guard (A, Key, I),
     Post => Inv (A, Key, I) and then I > I'Old
   is
   begin
      -- assignment
      Lemma_4 (A, Key, I);
      I := I + 1;
   end Search_4;

   procedure Search_3B (A : T_Arr; Key : T; I : in out Index_Type) with
     Pre => Inv (A, Key, I),
     Post => Inv (A, Key, I) and then not Guard (A, Key, I)
   is
   begin
      -- iteration
      pragma Assert (Inv (A, Key, I));
      while Guard (A, Key, I) loop
         Search_4 (A, Key, I);
         pragma Loop_Variant (Increases => I);
         pragma Loop_Invariant (Inv (A, Key, I));
      end loop;
   end Search_3B;

   procedure Lemma_3A (A : T_Arr; Key : T) with
     Ghost,
     Pre => A'Length > 0,
     Post => Inv (A, Key, A'First)
   is
   begin
      null;
   end Lemma_3A;

   procedure Search_3A (A : T_Arr; Key : T; I : out Index_Type) with
     Pre => A'Length > 0,
     Post => Inv (A, Key, I)
   is
   begin
      -- assignment
      Lemma_3A (A, Key);
      I := A'First;
   end Search_3A;

   function Result_Expression (A : T_Arr; Key : T; I : Index_Type) return Maybe_Index_Type
   is (if A (I) = Key then (Found => True, Index => I) else (Found => False))
   with Pre => I in A'Range;

   procedure Stronger_Postcondition (A : T_Arr; Key : T; I : Index_Type) with
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
   end Stronger_Postcondition;

   procedure Search_2 (A : T_Arr; Key : T; I : out Index_Type) with
     Pre => A'Length > 0,
     Post => I in A'Range and then Search_Post (A, Key, Result_Expression (A, Key, I))
   is
   begin
      -- sequential composition + strengthen postcondition
      Search_3A (A, Key, I);
      Search_3B (A, Key, I);
      Stronger_Postcondition (A, Key, I);
   end Search_2;

   function Search_1B (A : T_Arr; Key : T) return Maybe_Index_Type with
     Pre => A'Length > 0,
     Post => Search_Post (A, Key, Search_1B'Result)
   is
      I : Index_Type;
   begin
      -- introduce local variable + following assignment + contract frame
      Search_2 (A, Key, I);
      return Result_Expression (A, Key, I);
   end Search_1B;

   procedure Lemma_1A (A : T_Arr; Key : T)
     with Ghost,
     Pre => A'Length = 0,
     Post => Search_Post (A, Key, (Found => False))
   is
   begin
      null;
   end Lemma_1A;

   function Search_1A (A : T_Arr; Key : T) return Maybe_Index_Type with
     Pre => A'Length = 0,
     Post => Search_Post (A, Key, Search_1A'Result)
   is
      Result : Maybe_Index_Type;
   begin
      -- assignment
      Lemma_1A (A, Key);
      Result := (Found => False);
      return Result;
   end Search_1A;

   function Search (A : T_Arr; Key : T) return Maybe_Index_Type is
      Result : Maybe_Index_Type;
   begin
      -- alternation
      if A'Length = 0 then
         Result := Search_1A (A, Key);
      else
         Result := Search_1B (A, Key);
      end if;
      return Result;
   end Search;

end CCPR_Linear_Search;
