ghost predicate ExistsSubstring(str1: string, str2: string) {
	// string in Dafny is a sequence of characters (seq<char>) and <= on sequences is the prefix relation
	exists offset :: 0 <= offset <= |str1| && str2 <= str1[offset..]
}

ghost predicate Post(str1: string, str2: string, found: bool, i: nat) {
	(found <==> ExistsSubstring(str1, str2)) &&
	(found ==> i + |str2| <= |str1| && str2 <= str1[i..])
}

/*
Goal: Verify correctness of the following code. Once done, remove the {:verify false} (or turn it into {:verify true}).

Feel free to add GHOST code, including calls to lemmas. But DO NOT modify the specification or the original (executable) code.
*/
method {:verify false} FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
	ensures Post(str1, str2, found, i)
{
	if |str2| == 0 {
		found, i := true, 0;
	}
	else if |str1| < |str2| {
		found, i := false, 0; // value of i irrelevant in this case
	}
	else {
		found, i := false, |str2|-1;
		while !found && i < |str1|
		{
			var j := |str2|-1;
			while !found && str1[i] == str2[j]
			{
				if j == 0 {
					found := true;
				}
				else {
					i, j := i-1, j-1;
				}
			}
			if !found {
				i := i+|str2|-j;
			}
		}
	}
}

method Main() {
	var str1a, str1b := "string", " in Dafny is a sequence of characters (seq<char>)";
	var str1, str2 := str1a + str1b, "ring";
	var found, i := FindFirstOccurrence(str1, str2);
	assert found by {
		assert ExistsSubstring(str1, str2) by {
			var offset := 2;
			assert 0 <= offset <= |str1|;
			assert str2 <= str1[offset..] by {
				assert str2 == str1[offset..][..4];
			}
		}
	}
	print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
	if found {
		print " and i == ", i;
	}
	str1 := "<= on sequences is the prefix relation";
	found, i := FindFirstOccurrence(str1, str2);
	print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
	if found {
		print " and i == ", i;
	}
}