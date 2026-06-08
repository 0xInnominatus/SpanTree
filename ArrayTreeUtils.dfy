module {:extern "ArrayTreeUtils"} ArrayTreeUtils
{
	function Left(i: nat): nat { 2 * i + 1 }

	function Right(i: nat): nat { Left(i) + 1 }

	// Predicate to check if the subtree rooted at index is compact
	predicate IsCompact<T(!new)(==)(0)>(x: array<T>, empty: T, compare: (T, T) -> int, index: nat)
		reads x
		requires 0 <= index < x.Length
		decreases x.Length - index
	{
		if compare(x[index], empty) == 0 then
			if Right(index) < x.Length then
				IsCompact(x, empty, compare, Left(index)) && IsCompact(x, empty, compare, Right(index))
			else
				true
		else
			false
	}

	predicate LessIfNotEmpty<T(!new)(==)(0)>(a : T, b: T, empty: T, compare: (T, T) -> int)
	{
		if compare(a, empty) == 0 || compare(b, empty) == 0 then
			true
		else
			compare(a, b) < 0
	}

	predicate IsSorted<T(!new)(==)(0)>(x: array<T>, empty: T, compare: (T, T) -> int, index: nat)
		reads x
		requires 0 <= index < x.Length
		decreases x.Length - index
	{
		if compare(x[index], empty) == 0 then
			true
		else
			if Right(index) < x.Length then
				LessIfNotEmpty(x[Left(index)], x[Right(index)], empty, compare) &&
				LessIfNotEmpty(x[Left(index)], x[index], empty, compare) &&
				LessIfNotEmpty(x[index], x[Right(index)], empty, compare) &&
				IsSorted(x, empty, compare, Left(index)) &&
				IsSorted(x, empty, compare, Right(index))
			else
				true
	}

	predicate IsArrayTree<T(!new)(==)(0)>(x: array<T>, empty: T, compare: (T, T) -> int)
		reads x
		requires 0 < x.Length
		decreases x.Length
	{
		IsCompact(x, empty, compare, 0) &&
		IsSorted(x, empty, compare, 0)
	}

	method Add<T(!new)(==)(0)>(x: array<T>, item: T, empty: T, compare: (T, T) -> int)
		returns (position: nat)
		modifies x
		requires 0 < x.Length && IsArrayTree(x, empty, compare)
	{
		var index := 0;
		while index < x.Length && compare(x[index], empty) != 0
		{
			if compare(item, x[index]) == 0
			{
				return index;
			}
			else if compare(item, x[index]) < 0
			{
				index := Left(index);
			}
			else
			{
				index := Right(index);
			}
		}
		if (index < x.Length)
		{
			x[index] := item;
		}
		return index;
	}

	method IndexOf<T(!new)(==)(0)>(x: array<T>, item: T, empty: T, compare: (T, T) -> int)
		returns (position: int)
		ensures position != -1 ==> 0 <= position < x.Length && compare(item, x[position]) == 0
	{
		var index := 0;
		while index < x.Length && compare(x[index], empty) != 0
			invariant index >= 0
		{
			if compare(item, x[index]) == 0
			{
				return index;
			}
			else if compare(item, x[index]) < 0
			{
				index := Left(index);
			}
			else
			{
				index := Right(index);
			}
		}

		return -1;
	}

	method RemoveByIndex<T(!new)(==)(0)>(x: array<T>, index: nat, empty: T, compare: (T, T) -> int)
		requires 0 <= index < x.Length
		modifies x
		decreases x.Length - index
	{
		if (compare(x[index], empty) == 0)
		{
			return;
		}
		else
		{
			var rightIndex := Right(index);
			if rightIndex >= x.Length
			{
				x[index] := empty;
				return;
			}

			var leftIndex := rightIndex - 1;
			var leftComparison := compare(empty, x[leftIndex]);
			var rightComparison := compare(empty, x[rightIndex]);
			if (leftComparison == 0 && rightComparison == 0)
			{
				x[index] := empty;
			}
			else if (leftComparison == 0)
			{
				x[index] := x[rightIndex];
				RemoveByIndex(x, rightIndex, empty, compare);
			}
			else
			{
				x[index] := x[leftIndex];
				RemoveByIndex(x, leftIndex, empty, compare);
			}
		}
	}

	method Remove<T(!new)(==)(0)>(x: array<T>, item: T, empty: T, compare: (T, T) -> int)
		modifies x
	{
		var index := IndexOf(x, item, empty, compare);
		if index != -1
		{
			RemoveByIndex(x, index, empty, compare);
		}
	}
}
