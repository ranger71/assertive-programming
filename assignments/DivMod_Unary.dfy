// definitions borrowed from Rustan Leino's Program Proofs Chapter 7
// (https://program-proofs.com/code.html example code in Dafny; source file 7-Unary.dfy)
datatype Unary = Zero | Suc(pred: Unary)

ghost function UnaryToNat(x: Unary): nat {
  match x
  case Zero => 0
  case Suc(x') => 1 + UnaryToNat(x')
}

ghost function NatToUnary(n: nat): Unary {
  if n == 0 then Zero else Suc(NatToUnary(n-1))
}

lemma NatUnaryCorrespondence(n: nat, x: Unary)
  ensures UnaryToNat(NatToUnary(n)) == n
  ensures NatToUnary(UnaryToNat(x)) == x
{
}

predicate Less(x: Unary, y: Unary) {
  y != Zero && (x.Suc? ==> Less(x.pred, y.pred))
}

predicate LessAlt(x: Unary, y: Unary) {
  y != Zero && (x == Zero || Less(x.pred, y.pred))
}

lemma LessSame(x: Unary, y: Unary)
  ensures Less(x, y) == LessAlt(x, y)
{
}

lemma LessCorrect(x: Unary, y: Unary)
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
{
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
}

function Add(x: Unary, y: Unary): Unary {
  match y
  case Zero => x
  case Suc(y') => Suc(Add(x, y'))
}

lemma {:induction false} SucAdd(x: Unary, y: Unary)
  ensures Suc(Add(x, y)) == Add(Suc(x), y)
{
  match y
  case Zero =>
  case Suc(y') =>
    calc {
      Suc(Add(x, Suc(y')));
    ==  // def. Add
      Suc(Suc(Add(x, y')));
    ==  { SucAdd(x, y'); }
      Suc(Add(Suc(x), y'));
    ==  // def. Add
      Add(Suc(x), Suc(y'));
    }
}

lemma {:induction false} AddZero(x: Unary)
  ensures Add(Zero, x) == x
{
  match x
  case Zero =>
  case Suc(x') =>
    calc {
      Add(Zero, Suc(x'));
    ==  // def. Add
      Suc(Add(Zero, x'));
    ==  { AddZero(x'); }
      Suc(x');
    }
}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{
  match y
  case Zero => x
  case Suc(y') => Sub(x.pred, y')
}

function Mul(x: Unary, y: Unary): Unary {
  match x
  case Zero => Zero
  case Suc(x') => Add(Mul(x', y), y)
}

lemma SubStructurallySmaller(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures Sub(x, y) < x
{
}

lemma AddSub(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(Sub(x, y), y) == x
{
}

/*
Goal: implement correcly and clearly, using iterative code (no recursion), documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal

- DO NOT modify the specification or any of the definitions given in this file
- Not all definitions above are relevant, some are simply included as examples
- Feel free to use existing non-ghost functions/predicates in your code, and existing lemmas (for the proof) in your annotations
- New functions/predicates may be added ONLY as ghost
- If it helps you in any way, a recursive implementation + proof can be found in the book and the downloadable source file
  [https://program-proofs.com/code.html example code in Dafny, source file 7-Unary.dfy]
*/
method IterativeDivMod(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)

method Main() {
  var U3 := Suc(Suc(Suc(Zero)));
  assert UnaryToNat(U3) == 3;
  var U7 := Suc(Suc(Suc(Suc(U3))));
  assert UnaryToNat(U7) == 7;
  var d, m := IterativeDivMod(U7, U3);
  assert Add(Mul(d, U3), m) == U7 && Less(m, U3);
  print "Just as 7 divided by 3 is 2 with a remainder of 1, IterativeDivMod(", U7, ", ", U3, ") is ", d, " with a remainder of ", m;
}