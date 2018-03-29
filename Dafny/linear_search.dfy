  class Search{
    ghost var Contents: set<int>;
    var a : array<int>;

    predicate Valid()
        reads this, a;
    {
        a != null &&
        a.Length > 0 &&

        Contents == set x | 0 <= x < a.Length :: a[x]
    }

    constructor ()
        ensures fresh(a)
        ensures a != null;
        ensures a.Length == 4;
        ensures Valid();
    {
        a := new int[4](_ => 0);
        Contents := {0};
        new;
        assert a[0] == 0;
    }

    method data()
        modifies this, a;
        requires Valid();
        requires a.Length == 4;
        ensures Valid();
        ensures a.Length == 4;
    {
        a[0] := 0;
        a[1] := 1;
        a[2] := 2;
        a[3] := 3;
        Contents := {0, 1, 2, 3};
        assert a[0] == 0;
        assert a[1] == 1;
        assert a[2] == 2;
        assert a[3] == 3;
    }

    method search(e: int) returns (r: bool)
        modifies this, a;
        requires Valid();
        ensures Valid();
        ensures r == (e in Contents)
        ensures r == exists i: int :: 0 <= i < a.Length && a[i] == e
    {
        var index := 0;

        while (index < a.Length)
            invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != e
            decreases a.Length - index;
        {
            var removed := a[index];
            if (e == removed)
            {
                return true;
            }
            index := index + 1;
        }
        return false;
    }
  }

method Main()
{
    var s := new Search();
    s.data();
}