package body Squareroot with SPARK_Mode is

   procedure Lemma_Post (N : Big_Natural; A : Big_Natural) with Ghost,
     Pre => A**2 <= N and then not (N >= (A + 1) ** 2),
     Post => A**2 <= N and then N < (A + 1)**2
   is
   begin
      null;
   end Lemma_Post;

   procedure Lemma_Increment (N : Big_Natural; A : Big_Natural) with Ghost,
     Pre => A**2 <= N and then N >= (A + 1) ** 2,
     Post => (A+1)**2 <= N and then 0 <= N - (A+1)**2 and then  N - (A+1)**2 < N - A ** 2
   is
   begin
      null;
   end Lemma_Increment;

   procedure Lemma_Init (N : Big_Natural) with Ghost,
     Post => 0**2 <= N
   is
   begin
      null;
   end Lemma_Init;

   procedure Sqrt (N : in Big_Natural; A : out Big_Natural)
   is
   begin
      Lemma_Init (N);
      A := 0;
      pragma Assert (A**2 <= N);
      while N >= (A + 1) ** 2 loop
         Lemma_Increment (N, A);
         A := A + 1;
         -- pragma Loop_Variant (Decreases => N - A**2);
         pragma Loop_Invariant (A**2 <= N);
      end loop;
      -- pragma Annotate (GNATprove, False_Positive, "terminating annotation",
      --                  "That version of SPARK does not allow variant on Big_Natural");
      Lemma_Post (N, A);
   end Sqrt;

end Squareroot;
