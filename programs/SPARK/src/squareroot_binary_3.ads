with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package Squareroot_Binary_3 with SPARK_Mode is

   procedure Sqrt (N : in Big_Integer; A : out Big_Integer)
   with
       Pre => 0 <= N,
       Post => A**2 <= N and then N < (A + 1)**2;

   procedure Sqrt_the_code (N : in Big_Integer; A : out Big_Integer)
   with
       Pre => 0 <= N,
       Post => A**2 <= N and then N < (A + 1)**2;

   procedure Sqrt_non_terminating (N : in Big_Integer; A : out Big_Integer)
   with
       Pre => 0 <= N,
       Post => A**2 <= N and then N < (A + 1)**2;

end Squareroot_Binary_3;
