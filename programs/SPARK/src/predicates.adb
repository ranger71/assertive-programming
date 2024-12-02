package body Predicates with SPARK_Mode is

   procedure Occ_Eq (A, B : T_Arr; E : T) with
     Pre  => A = B,
     Post => Occ (A, E) = Occ (B, E);

   procedure Occ_Eq (A, B : T_Arr; E : T) is
      begin
      if A'Length = 0 then
         return;
      end if;

      if A (A'Last) = E then
         pragma Assert (B (B'Last) = E);
      else
         pragma Assert (B (B'Last) /= E);
      end if;

      Occ_Eq (Remove_Last (A), Remove_Last (B), E);
   end Occ_Eq;


   procedure Occ_Set
     (A : T_Arr;
      B : T_Arr;
      J : Positive;
      V : T;
      E : T)
   is
      C : T_Arr:= Remove_Last (A);
   begin
      if A'Length = 0 then
         return;
      end if;

      if J = A'Last then
         Occ_Eq (C, Remove_Last (B), E);
      else
         C (J) := V;
         Occ_Eq (Remove_Last (B), C, E);
         Occ_Set (Remove_Last (A), C, J, V, E);
      end if;
   end Occ_Set;

end Predicates;
