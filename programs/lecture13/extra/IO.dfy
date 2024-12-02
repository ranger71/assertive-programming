class IO<T> {
	var alpha: seq<T>, omega: seq<T>;

	method Input() returns (x: T)
		requires !EOF() //alpha != []
		modifies this
		ensures omega == old(omega)
		ensures old(alpha) == [x] + alpha
	{
		x, alpha := alpha[0], alpha[1..];
	}

	method Output(x: T)
		modifies this
		ensures alpha == old(alpha)
		ensures omega == old(omega) + [x]
	{
		omega := omega + [x];
	}

	method Rewrite()
		modifies this
		ensures omega == []
		ensures alpha == old(alpha)
	{
		omega := [];
	}

	predicate EOF() reads this { alpha == [] }

}
