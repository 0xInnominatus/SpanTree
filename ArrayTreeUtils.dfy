module {:extern "ArrayTreeUtils"} ArrayTreeUtils
{
	function Left(i: nat): nat { 2 * i + 1 }
	function Right(i: nat): nat { Left(i) + 1 }

	method Add<T(!new)(==)(0)>(x: array<T>, item: T, empty: T, compare: (T, T) -> int)
		returns (position: nat)
		modifies x
	{
		var index := 0;
		while index < x.Length && x[index] != empty
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
		while index < x.Length && x[index] != empty
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
