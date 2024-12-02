package body Squareroot_Binary with SPARK_Mode is

   function Inv (N : Big_Integer; A, B : Big_Integer) return Boolean is
      (0 <= A and then A < B and then A**2 <= N and then N < B**2)
      with Ghost;

   -- see how this guard was derived in Lemma_Update_Left_Bound (#)
   function Guard (N : Big_Integer; M : Big_Integer) return Boolean is
      (M**2 <= N);

   procedure Lemma_Update_Right_Bound (N : Big_Integer; M, A, B : Big_Integer) with Ghost,
      Pre => Inv (N, A, B) and then A < M and then M < B and then not Guard (N, M),
      Post => Inv (N, A, M) and then 0 <= M - A and then M - A < B - A
   is
   begin
      -- similarly to Lemma_Update_Left_Bound below (having already derived the definition of "Guard" there):
      pragma Assert (0 <= A);        -- from Inv
      pragma Assert (A < M);         -- from Pre
      pragma Assert (A**2 <= N);     -- from Inv
      pragma Assert (N < M**2);      -- from the negation of the Guard in Pre
      pragma Assert (0 <= M - A);    -- from "A < M" in Pre
      pragma Assert (M - A < B - A); -- from "M < B" in Pre
   end Lemma_Update_Right_Bound;

   procedure Lemma_Update_Left_Bound (N : Big_Integer; M, A, B : Big_Integer) with Ghost,
     Pre => Inv (N, A, B) and then A < M and then M < B and then Guard (N, M),
     Post => Inv (N, M, B) and then 0 <= B - M and then B - M < B - A
   is
   begin
      -- SPARK proves this by itself, here's why (for the human reader):
      pragma Assert (0 <= M);        -- from "0 <= A" (Inv) and the "A < M" in Pre
      pragma Assert (M < B);         -- from Pre
      pragma Assert (M**2 <= N);     -- see comment (#) below
      pragma Assert (N < B**2);      -- from Inv
      pragma Assert (0 <= B - M);    -- from "M < B" in Pre
      pragma Assert (B - M < B - A); -- from "A < M" in Pre
      -- property (#) above is the only portion of Post that is
      -- not guaranteed by the first three conjuncts of Pre;
      -- so let's define (derive!) the Guard with this expression
   end Lemma_Update_Left_Bound;

   procedure Lemma_Mid (N : Big_Integer; M, A, B : Big_Integer) with
     Ghost,
     Pre => Inv (N, A, B) and then A + 1 /= B and then M = (A + B) / 2,
     Post => Inv (N, A, B) and then A < M and then M < B
   is
   begin
      -- SPARK proves this by itself, here's why (for the human reader):
      pragma Assert (Inv (N, A, B)); -- from Pre
      -- the average of any two non-consecutive integers
      -- (never mind if rounded up or down) is in between the two
      pragma Assert (B - A >= 2); -- by the "A < B" (Inv) and the second conjunct of Pre
      pragma Assert (A < (A + B) / 2); -- by the assertion above (and arithmetic)
      pragma Assert ((A + B) / 2 < B); -- same reason
   end Lemma_Mid;

   procedure Lemma_Init (N : Big_Integer) with Ghost,
     Pre => 0 <= N,
     Post => Inv (N, 0, N+1)
   is
   begin
      -- SPARK proves this by itself, here's why (for the human reader):
      pragma Assert (0 <= 0);       -- trivial
      pragma Assert (0 < N+1);      -- from Pre (and arithmetic)
      pragma Assert (0**2 <= N);    -- from Pre
      pragma Assert (N < (N+1)**2); -- true for all integers (arithmetic), let alone the non-negative ones
   end Lemma_Init;

   procedure Lemma_Stronger_Postcondition (N : Big_Integer; A, B : Big_Integer) with Ghost,
     Pre => Inv (N, A, B) and then A + 1 = B,
     Post => A**2 <= N and then N < (A + 1)**2
   is
   begin
      null; -- follows from Inv with substitution of "A + 1" for the "B"
   end Lemma_Stronger_Postcondition;

   procedure Sqrt (N : in Big_Integer; A : out Big_Integer)
   is
      B : Big_Integer;
      M : Big_Integer;
   begin
      Lemma_Init (N);
      A := 0;
      B := N + 1;
      pragma Assert (Inv (N, A, B));
      while A + 1 /= B loop
         M := (A + B) / 2;
         Lemma_Mid (N, M, A, B);
         pragma Assert (Inv (N, A, B) and then A < M and then M < B);
         if M**2 <= N then -- Guard (N, M) then
            Lemma_Update_Left_Bound (N, M, A, B);
            A := M;
         else
            Lemma_Update_Right_Bound (N, M, A, B);
            B := M;
         end if;
         -- pragma Loop_Variant (Decreases => B - A);
         pragma Loop_Invariant (Inv (N, A, B));
      end loop;
      -- pragma Annotate (GNATprove, False_Positive, "terminating annotation",
      --                  "That version of SPARK does not allow variant on Big_Natural");
      Lemma_Stronger_Postcondition (N, A, B);
   end Sqrt;

end Squareroot_Binary;
