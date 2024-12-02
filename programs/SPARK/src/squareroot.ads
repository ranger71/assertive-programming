with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package Squareroot with SPARK_Mode is

   procedure Sqrt (N : in Big_Natural; A : out Big_Natural)
   with
     Post => A**2 <= N and then N < (A + 1)**2;

end Squareroot;
