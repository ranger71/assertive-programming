with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package Squareroot_Binary with SPARK_Mode is

   procedure Sqrt (N : in Big_Integer; A : out Big_Integer)
   with
     Pre => 0 <= N,
     Post => A**2 <= N and then N < (A + 1)**2;

end Squareroot_Binary;
