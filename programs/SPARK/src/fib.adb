package body Fib with SPARK_Mode is

   function Inv (N, I : Big_Natural; A, B : Big_Natural) return Boolean is
     (2 <= I and then I <= N and then A = Fib_Number (I - 1) and then B = Fib_Number (I))
       with Ghost;

   procedure Lemma_Post (N, I : in Big_Natural; A, B : in Big_Natural) with Ghost,
     Pre => Inv (N, I, A, B) and then I = N,
     Post => B = Fib_Number (N)
   is
   begin
      pragma Assert (B = Fib_Number (I) and then I = N);
   end Lemma_Post;

   procedure Lemma_Init (N : in Big_Natural) with Ghost,
     Pre => N >= 2,
     Post => Inv (N, 2, 1, 1)
   is
   begin
      null;
   end Lemma_Init;

   procedure Lemma_Iteration (N, I : in Big_Natural; A, B : in Big_Natural) with Ghost,
     Pre => Inv (N, I, A, B) and then I /= N,
     Post => Inv (N, I + 1, B, A + B) and then I < I + 1 and then I + 1 <= N
   is
   begin
      null;
   end Lemma_Iteration;

   procedure Lemma_Base_Cases (N : in Big_Natural) with Ghost,
     Pre => N < 2,
     Post => N = Fib_Number (N)
   is
   begin
      null;
   end Lemma_Base_Cases;

   procedure Compute_Fib (N : in Big_Natural; B : out Big_Natural)
   is
   begin
      if N < 2 then
         Lemma_Base_Cases (N);
         B := N;
      else
         declare
            I : Big_Natural;
            A : Big_Natural;
            Previous_A : Big_Natural;
         begin
            Lemma_Init (N);
            A := 1;
            B := 1;
            I := 2;
            pragma Assert (Inv (N, I, A, B));
            while I /= N loop
               Lemma_Iteration (N, I, A, B);
               -- the effect of this sequence is like a multiple assignment "A, B, I := B, A + B, I + 1"
               Previous_A := A;
               A := B;
               B := Previous_A + B;
               I := I + 1;
               -- pragma Loop_Variant (Increases => I);
               -- or "Decreases => N-I" if Increases does not work for Big_Natural
               pragma Loop_Invariant (Inv (N, I, A, B));
            end loop;
            Lemma_Post (N, I, A, B);
         end;
      end if;
   end Compute_Fib;

end Fib;
