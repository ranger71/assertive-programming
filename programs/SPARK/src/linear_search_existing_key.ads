package Linear_Search_Existing_Key with SPARK_Mode is

   type T is new Integer;
   type Index_Base_Type is new Natural;
   subtype Index_Type is Index_Base_Type range Index_Base_Type'First + 1 .. Index_Base_Type'Last - 1;
   type T_Arr is array (Index_Type range <>) of T;

   procedure Search (A : T_Arr; Key : T; I : out Index_Type)
     with
       Pre => (for some J in A'Range => A (J) = Key),
       Post => I in A'Range and then A (I) = Key;

end Linear_Search_Existing_Key;
