with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package Fib with SPARK_Mode is

   function Fib_Number (N : Big_Natural) return Big_Natural is
     (if N = 0 then To_Big_Integer (0) elsif N = 1 then To_Big_Integer (1)
      else Fib_Number (N - 2) + Fib_Number (N - 1))
   with Ghost,
     Annotate => (GNATprove, Terminating),
     Annotate => (GNATprove, False_Positive, "terminating annotation",
                  "That version of SPARK does not allow variant on Big_Natural");

   procedure Compute_Fib (N : in Big_Natural; B : out Big_Natural)
     with
       Post => B = Fib_Number (N);

end Fib;
