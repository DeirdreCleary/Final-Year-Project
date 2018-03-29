include "hashset_interface.dfy"

module ChainingHashset refines HashsetInterface{
  datatype Item = Empty | Tombstone | Entry(i: int)

  class Hashset{
    var a : array2<Item>;

    predicate ValidArray(arr: array2)
        reads this, Repr;
    {
        0 < arr.Length0 &&
        0 < arr.Length1 &&
        arr in Repr
    }

    predicate Valid()
    {
        ValidArray(a) &&
        Exclusivity() &&
        (forall e :: e in Contents ==> (exists i :: 0 <= i < a.Length1 && a[hash(e),i].Entry? && a[hash(e),i].i == e)) &&
        (forall h,i :: 0 <= h < a.Length0 && 0 <= i < a.Length1 && a[h,i].Entry? ==> a[h,i].i in Contents)
    }

    predicate Exclusivity()
        reads this, Repr;
        reads a;
    {
        forall i: int, j: int, k: int, l: int ::
            0 <= i < a.Length0 && 0 <= j < a.Length0 &&
            0 <= k < a.Length1 && 0 <= l < a.Length1 &&
            (i!=j || l != k) &&
            a[i,k].Entry? && a[j,l].Entry?
                ==> a[i,k].i != a[j,l].i
    }

    constructor (size: int)
        ensures fresh(a);
        ensures Repr == {a};
        ensures 0 < a.Length0;
    {
        a := new Item[size,10]((x,y) => Empty);
        Contents := {};
        Repr := {a};
    }

    method insert(e: int) returns (r: bool)
        ensures a == old(a);
        ensures !r ==> forall i: int, k: int :: 0 <= i < a.Length0 && 0 <= k < a.Length1 && a[i,k].Entry? ==> a[i,k].i != e;
        ensures r ==> exists i: int, k: int :: 0 <= i < a.Length0 && 0 <= k < a.Length1 && a[i,k].Entry? ==> a[i,k].i == e;
    {
        var index := get(e);
        if(index > -1){
            r := true;
        }
        else{
            var firstEmpty := getEmpty(e);
            if(firstEmpty > -1){
                a[hash(e),firstEmpty] := Entry(e);
                Contents := Contents + {e};

                assert a[hash(e),firstEmpty].Entry? && a[hash(e),firstEmpty].i == e;
                assert forall i, k :: (0 <= i < a.Length0 && 0 <= k < a.Length1 && (i!=hash(e) || k!=firstEmpty)) ==> a[i,k] == old(a[i,k]);
                assert (forall e :: e in Contents ==> (exists h, i :: h == hash(e) && 0 <= i < a.Length1 && a[h,i].Entry? && a[h,i].i == e));

                r := true;
            }
            else{
                r := false;
            }
        }
    }

    method remove(e: int) returns (r: bool)
        ensures a == old(a);
        ensures forall i, k :: (0 <= i < a.Length0 && 0 <= k < a.Length1 && a[i,k].Entry?) ==> a[i,k].i != e;
    {
        var index := get(e);
        if(index == -1){
            r := false;
        }
        else{
            a[hash(e),index] := Tombstone;
            Contents := Contents - {e};

            assert forall i, k :: (0 <= i < a.Length0 && 0 <= k < a.Length1 && (i!=hash(e) || (k!=index))) ==> a[i,k] == old(a[i,k]);
            assert (forall e :: e in Contents ==> (exists h, i :: h == hash(e) && 0 <= i < a.Length1 && a[h,i].Entry? && a[h,i].i == e));

            r := true;
        }
    }

    method get(e: int) returns (r: int)
        ensures r < a.Length1;
        ensures (r == -1) ==> forall i: int, k: int :: (0 <= i < a.Length0 && 0 <= k < a.Length1 && a[i,k].Entry?) ==> a[i,k].i != e;
        ensures (r >= 0) ==> (a[hash(e),r].Entry? && a[hash(e),r].i == e);
    {
        var getItem := Entry(e);
        var index := 0;

        while (index < a.Length1)
            invariant Valid();
            invariant forall k :: 0 <= k < index && k < a.Length1 ==> a[hash(e),k] != getItem;
            decreases a.Length1 - index;
        {
            var removed := a[hash(e),index];
            if (getItem == removed)
            {
                r := index;
                return;
            }
            index := index + 1;
        }
        r := -1;
    }

    method getEmpty(e: int) returns (r: int)
        requires Valid();
        ensures Valid();
        ensures Repr == old(Repr);
        ensures r < a.Length1;
        ensures (r == -1) ==> forall k: int :: (0 <= k < a.Length1) ==> !a[hash(e),k].Empty?;
        ensures (r >= 0) ==> (a[hash(e),r].Empty?);
    {
        var getItem := Empty;
        var index := 0;

        while (index < a.Length1)
            invariant Valid();
            invariant forall k :: 0 <= k < index && k < a.Length1 ==> a[hash(e),k] != getItem;
            decreases a.Length1 - index;
        {
            if (a[hash(e),index].Empty?)
            {
                r := index;
                return;
            }
            index := index + 1;
        }
        r := -1;
    }

    function method hash(e: int) : int
        reads this, Repr;
        requires 0 < a.Length0;
    {
        // (31 * (17 + e)) % a.Length
        e % a.Length0
    }
  }

    method Main()
    {
        var hs := new Hashset(10);
        var i := hs.insert(1);
        var j := hs.get(1);
        var k := hs.insert(2);
        var l := hs.get(2);
        var m := hs.insert(5);
        var n := hs.get(5);
        print(j);
        print(l);
        print(m);
    }
}