package body Squareroot_Binary_3 with SPARK_Mode is

   function Inv (N, A, B : Big_Integer) return Boolean is
     (0 <= A and then A < B and then A**2 <= N and then N < B**2)
     with Ghost;

   function Guard (N, M : Big_Integer) return Boolean is
     (M**2 <= N); -- derived from the proof obligations (Lemma_Update_A)

   procedure Lemma_Init (N : Big_Integer) with Ghost,
     Pre => 0 <= N,
     Post => Inv (N, 0, N + 1)
   is
   begin
      pragma Assert (0 <= N);
      -- the lemma precondition should guarantee correctness of its
      -- postcondition (as confirmed by GNATprove):
      pragma Assert (0 <= 0);
      pragma Assert (0 < N + 1);
      pragma Assert (0**2 <= N);
      pragma Assert (N < (N + 1)**2);
   end Lemma_Init;

   procedure Lemma_Update_A (N, A, M, B, V0 : Big_Integer)
     with Ghost,
     Pre => Inv (N, A, B) and then B /= A + 1 and then
     M = (A + B) / 2 and then V0 = B - A and then Guard (N, M),
     Post => Inv (N, M, B) and then 0 <= B - M and then B - M < V0
   is
   begin
      -- recall the lemma precondition:
      pragma Assert (0 <= A);          -- pre0a
      pragma Assert (A < B);           -- pre0b
      pragma Assert (A**2 <= N);       -- pre1a
      pragma Assert (N < B**2);        -- pre1b
      pragma Assert (B /= A + 1);      -- pre2
      pragma Assert (M = (A + B) / 2); -- pre3
      pragma Assert (V0 = B - A);      -- pre4
      pragma Assert (Guard (N, M));    -- pre5
      -- and the details of the lemma postconditions:
      pragma Assert (0 <= M);     -- from pre0a,b + pre3
      pragma Assert (M < B);      -- from pre0a,b + pre3
      pragma Assert (M**2 <= N);  -- missing: define the guard (pre5) this way
      pragma Assert (N < B**2);   -- from pre1b
      pragma Assert (0 <= B - M); -- from the "M < B" above
      pragma Assert (B - M < V0); -- from pre4 and "A < M" from pre0b,2,3
   end Lemma_Update_A;

   procedure Lemma_Update_B (N, A, M, B : Big_Integer; V0 : Big_Integer)
     with Ghost,
     Pre => Inv (N, A, B) and then B /= A + 1 and then
     M = (A + B) / 2 and then V0 = B - A and then not Guard (N, M),
     Post => Inv (N, A, M) and then 0 <= M - A and then M - A < V0
   is
   begin
      -- recall the lemma precondition (after derivation of the guard):
      pragma Assert (0 <= A);          -- pre0a
      pragma Assert (A < B);           -- pre0b
      pragma Assert (A**2 <= N);       -- pre1a
      pragma Assert (N < B**2);        -- pre1b
      pragma Assert (B /= A + 1);      -- pre2
      pragma Assert (M = (A + B) / 2); -- pre3
      pragma Assert (V0 = B - A);      -- pre4
      pragma Assert (not (M**2 <= N)); -- pre5
      -- and the details of the lemma postconditions:
      pragma Assert (0 <= A);     -- from pre0a
      pragma Assert (A < M);      -- from pre0b,2,3
      pragma Assert (A**2 <= N);  -- from pre1a
      pragma Assert (N < M**2);   -- from pre4 (negation of the guard)
      pragma Assert (0 <= M - A); -- from the "A < M" above
      pragma Assert (M - A < V0); -- from pre4 and "M < B" from pre0a,b + pre3
   end Lemma_Update_B;

   procedure Lemma_Stronger_Postcondition (N, A, B : Big_Integer) with Ghost,
     Pre => Inv (N, A, B) and then B = A + 1,
     Post => A**2 <= N and then N < (A + 1)**2
   is
   begin
      null; -- by design (of Inv)
   end Lemma_Stronger_Postcondition;

   procedure Sqrt (N : in Big_Integer; A : out Big_Integer) is
      B, M : Big_Integer;
      V0 : Big_Integer with Ghost;
   begin
      pragma Assert (0 <= N); -- the precondition
      Lemma_Init (N);
      pragma Assert (Inv (N, 0, N + 1));
      A := 0;
      pragma Assert (Inv (N, A, N + 1));
      B := N + 1;
      pragma Assert (Inv (N, A, B));
      while B /= A + 1 loop
         V0 := B - A;
         M := (A + B) / 2; -- no risk of overflow
         pragma Assert (Inv (N, A, B));
         pragma Assert (B /= A + 1);
         pragma Assert (M = (A + B) / 2); -- "A < M and then M < B" suffices
         pragma Assert (V0 = B - A);
         if M**2 <= N then -- Guard (N, M)
            pragma Assert (Inv (N, A, B));
            pragma Assert (B /= A + 1);
            pragma Assert (M = (A + B) / 2);
            pragma Assert (V0 = B - A);
            pragma Assert (Guard (N, M));
            Lemma_Update_A (N, A, M, B, V0);
            pragma Assert (0 <= B - M and then B - M < V0);
            pragma Assert (Inv (N, M, B));
            A := M;
            pragma Assert (0 <= B - A and then B - A < V0);
            pragma Assert (Inv (N, A, B));
         else
            pragma Assert (Inv (N, A, B));
            pragma Assert (B /= A + 1);
            pragma Assert (M = (A + B) / 2);
            pragma Assert (V0 = B - A);
            pragma Assert (not Guard (N, M));
            Lemma_Update_B (N, A, M, B, V0);
            pragma Assert (0 <= M - A and then M - A < V0);
            pragma Assert (Inv (N, A, M));
            B := M;
            pragma Assert (0 <= B - A and then B - A < V0);
            pragma Assert (Inv (N, A, B));
         end if;
         pragma Assert (0 <= B - A and then B - A < V0);
         pragma Loop_Invariant (Inv (N, A, B));
         -- pragma Loop_Variant (Decreases => B - A);
      end loop;
      -- pragma Annotate (GNATprove, False_Positive, "terminating annotation",
      --                  "That version of SPARK does not allow variant on Big_Integer");
      pragma Assert (Inv (N, A, B) and then B = A + 1);
      Lemma_Stronger_Postcondition (N, A, B);
      pragma Assert (A**2 <= N and then N < (A + 1)**2); -- the postcondition
   end Sqrt;

   procedure Sqrt_the_code (N : in Big_Integer; A : out Big_Integer) is
     B, M : Big_Integer;
   begin
      A := 0;
      B := N + 1;
      while B /= A + 1 loop
         M := (A + B) / 2;
         if M**2 <= N then
            A := M;
         else
            B := M;
         end if;
         pragma Loop_Invariant (Inv (N, A, B));
      end loop;
   end Sqrt_the_code;

   procedure Sqrt_non_terminating (N : in Big_Integer; A : out Big_Integer) is
     B, M : Big_Integer;
   begin
      A := 0;
      B := N + 1;
      while B /= A + 1 loop
         M := 0;--(A + B) / 2;
         if M**2 <= N then
            A := M;
         else
            B := M;
         end if;
         pragma Loop_Invariant (Inv (N, A, B));
      end loop;
   end Sqrt_non_terminating;

end Squareroot_Binary_3;
