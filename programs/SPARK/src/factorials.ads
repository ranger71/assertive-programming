with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package Factorials with SPARK_Mode is

   function Factorial (N : Big_Integer) return Big_Integer is
     (if N = 0 then To_Big_Integer (1) else Factorial (N - 1) * N)
       with
         Ghost,
         Pre => N >= 0,
         Annotate => (GNATprove, Terminating),
         Annotate => (GNATprove, False_Positive, "terminating annotation",
                  "That version of SPARK does not allow variant on Big_Integer");

   procedure Compute_Factorial (N : in Big_Integer; F : out Big_Integer)
     with
       Pre => N >= 0,
       Post => F = Factorial (N);

   procedure Compute_Factorial_Down_loop (N : in Big_Integer; F : out Big_Integer)
     with
       Pre => N >= 0,
       Post => F = Factorial (N);

end Factorials;
