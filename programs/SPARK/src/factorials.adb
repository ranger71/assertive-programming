package body Factorials with SPARK_Mode is

   function Inv (N, I : Big_Integer; F : Big_Integer) return Boolean is
     (0 <= I and then I <= N and then F = Factorial (I))
       with Ghost;

   procedure Lemma_Init (N : in Big_Integer) with Ghost,
     Pre => N >= 0,
     Post => Inv (N, 0, 1)
   is
   begin
      null;
   end Lemma_Init;

   procedure Lemma_Iteration (N, I : in Big_Integer; F : in Big_Integer) with Ghost,
     Pre => Inv (N, I, F) and then I /= N,
     Post => Inv (N, I + 1, F * (I + 1)) and then I < I + 1
   is
   begin
      null;
   end Lemma_Iteration;

   procedure Lemma_Post (N, I : in Big_Integer; F : in Big_Integer) with Ghost,
     Pre => Inv (N, I, F) and then I = N,
     Post => F = Factorial (N)
   is
   begin
      null;
   end Lemma_Post;

   procedure Compute_Factorial (N : in Big_Integer; F : out Big_Integer)
   is
      I : Big_Integer;
   begin
      Lemma_Init (N);
      F := 1;
      I := 0;
      pragma Assert (Inv (N, I, F));
      while I /= N loop
         Lemma_Iteration (N, I, F);
         F := F * (I + 1);
         I := I + 1;
         -- pragma Loop_Variant (Increases => I);
         pragma Loop_Invariant (Inv (N, I, F));
      end loop;
      Lemma_Post (N, I, F);
   end Compute_Factorial;

   function Inv2 (N, I : Big_Integer; F : Big_Integer) return Boolean is
     (0 <= I and then I <= N and then F * Factorial (I) = Factorial (N))
       with Ghost;

   procedure Lemma_Init2 (N : in Big_Integer) with Ghost,
     Pre => N >= 0,
     Post => Inv2 (N, N, 1)
   is
   begin
      null;
   end Lemma_Init2;

   procedure Lemma_Iteration2 (N, I : in Big_Integer; F : in Big_Integer) with Ghost,
     Pre => Inv2 (N, I, F) and then I > 1,
     Post => Inv2 (N, I - 1, F * I) and then 0 <= I - 1 and then I - 1 < I
   is
   begin
      null;
   end Lemma_Iteration2;

   procedure Lemma_Post2 (N, I : in Big_Integer; F : in Big_Integer) with Ghost,
     Pre => Inv2 (N, I, F) and then I <= 1,
     Post => F = Factorial (N)
   is
   begin
      null;
   end Lemma_Post2;

   procedure Compute_Factorial_Down_loop (N : in Big_Integer; F : out Big_Integer)
   is
      I : Big_Integer;
   begin
      Lemma_Init2 (N);
      F := 1;
      I := N;
      pragma Assert (Inv2 (N, I, F));
      while I > 1 loop
         Lemma_Iteration2 (N, I, F);
         F := F * I;
         I := I - 1;
         -- pragma Loop_Variant (Decreases => I);
         pragma Loop_Invariant (Inv2 (N, I, F));
      end loop;
      Lemma_Post2 (N, I, F);
   end Compute_Factorial_Down_loop;

end Factorials;
