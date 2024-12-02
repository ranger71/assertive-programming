package Linear_Search with SPARK_Mode is

   type T is new Integer;
   type Index_Base_Type is new Natural;
   subtype Index_Type is Index_Base_Type range Index_Base_Type'First + 1 .. Index_Base_Type'Last - 1;
   type T_Arr is array (Index_Type range <>) of T;
   type Maybe_Index_Type (Found : Boolean := False) is record
      case Found is
      when True =>
         Index : Index_Type;
      when False =>
         null;
      end case;
   end record;

   function Search_Post (A : T_Arr; Key : T; Result : Maybe_Index_Type) return Boolean is
     ((Result.Found = (for some I in A'Range => A (I) = Key)) and then
          (if Result.Found then Result.Index in A'Range and then A (Result.Index) = Key))
         with Ghost;

   function Search (A : T_Arr; Key : T) return Maybe_Index_Type
     with
       Post => Search_Post (A, Key, Search'Result);

end Linear_Search;
