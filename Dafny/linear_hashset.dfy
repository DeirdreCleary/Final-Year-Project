include "hashset_interface.dfy"

module LinearHashset refines HashsetInterface{
  datatype Item = Empty | Tombstone | Entry(i: int)

  class Hashset{
    var a : array<Item>;

    predicate ValidArray(arr: array)
        reads this, Repr;
    {
        0 < arr.Length &&
        arr in Repr
    }

    predicate Valid()
    {
        ValidArray(a) &&
        Exclusivity() &&
        (Contents == set x: int | 0 <= x < a.Length && a[x].Entry? :: a[x].i) &&
        forall e :: e in Contents ==> (exists i :: 0 <= i < a.Length && a[i].Entry? && a[i].i == e && CheckSlots(hash(e), i, Empty))
    }

    predicate Exclusivity()
        reads this, a;
    {
        forall i: int, j: int :: 0 <= i < a.Length && 0 <= j < a.Length && j != i && a[i].Entry? && a[j].Entry?
             ==> a[i].i != a[j].i
    }

    constructor (size: int)
        ensures fresh(a);
        ensures 0 < a.Length;
        ensures Valid();
    {
        a := new Item[size](_ => Empty);
        Repr := {a};
        Contents := {};
    }

    method insert(e: int) returns (r: bool)
        ensures a == old(a);
        ensures !r == forall j: int :: 0 <= j < a.Length && a[j].Entry? ==> a[j].i != e;
        ensures r == exists j: int :: 0 <= j < a.Length && a[j].Entry? && a[j].i == e;
    {
        var index := get(e);
        if(index > -1){
            r := true;
        }
        else{
            var firstEmpty := getEmpty(e);
            if(firstEmpty > -1){
                a[firstEmpty] := Entry(e);
                Contents := Contents + {e};

                assert a[firstEmpty].Entry? && a[firstEmpty].i == e;
                assert forall j: int :: 0 <= j < a.Length && j != firstEmpty ==> a[j] == old(a[j]);
                assert CheckSlots(hash(e), firstEmpty, Empty);

                r := true;
            }
            else{
                r := false;
            }
        }
    }

    method remove(e: int) returns (r: bool)
        ensures a == old(a);
        ensures forall j: int :: 0 <= j < a.Length && a[j].Entry? ==> a[j].i != e;
    {
        var index := get(e);
        if(index == -1){
            r := false;
        }
        else{
            a[index] := Tombstone;
            Contents := Contents - {e};

            assert forall j: int :: 0 <= j < a.Length && j != index ==> a[j] == old(a[j]);

            r := true;
        }
    }

    method get(e: int) returns (r: int)
        ensures r < a.Length;
        ensures (r == -1) ==> CheckSlots(0, a.Length, Entry(e))
        ensures (r >= 0) ==> (a[r].Entry? && a[r].i == e);
    {
        var originalSlot := hash(e);
        var slotsChecked : nat := 0;
        var getItem := Entry(e);
        var curSlot := originalSlot;

        while (slotsChecked < a.Length)
            invariant Valid();
            invariant slotsChecked <= a.Length;
            invariant 0 <= curSlot < a.Length;
            invariant slotsChecked + originalSlot <  a.Length ==>
                CheckSlotsSimple(originalSlot, slotsChecked + originalSlot, getItem) &&
                CheckSlotsSimple(originalSlot, slotsChecked + originalSlot, Empty);
            invariant slotsChecked + originalSlot >= a.Length ==>
                CheckSlotsSimple(0, (slotsChecked + originalSlot) - a.Length, getItem) &&
                CheckSlotsSimple(originalSlot, a.Length, getItem) &&
                CheckSlotsSimple(0, (slotsChecked + originalSlot) - a.Length, Empty) &&
                CheckSlotsSimple(originalSlot, a.Length, Empty);
            decreases a.Length - slotsChecked;
        {
            curSlot := (originalSlot + slotsChecked) % a.Length;
            if (a[curSlot] == getItem)
            {
                r := curSlot;
                return;
            }
            if (a[curSlot].Empty?)
            {
                r := -1;
                assert e !in Contents;
                return;
            }
            slotsChecked := slotsChecked + 1;
            assert slotsChecked + originalSlot >= a.Length ==>
                CheckSlotsSimple(0, (slotsChecked + originalSlot) - a.Length, getItem) &&
                CheckSlotsSimple(originalSlot, a.Length, getItem) &&
                CheckSlotsSimple(0, (slotsChecked + originalSlot) - a.Length, Empty) &&
                CheckSlotsSimple(originalSlot, a.Length, Empty);
        }
        assert e !in Contents;
        r := -1;
    }

    predicate CheckSlotsSimple(fromSlot: int, toSlot: int, e: Item)
        reads this, a;
        requires a.Length > 0;
        requires 0 <= fromSlot <= toSlot <= a.Length;
    {
        forall k :: 0 <= fromSlot <= k < toSlot ==> a[k] != e
    }

    predicate CheckSlots(fromSlot: int, toSlot: int, e: Item)
        reads this, a;
        requires a.Length > 0;
        requires 0 <= fromSlot <= a.Length && 0 <= toSlot <= a.Length;
    {
        (fromSlot < toSlot ==>  CheckSlotsSimple(fromSlot, toSlot, e)) &&
        (fromSlot > toSlot ==> (CheckSlotsSimple(fromSlot, a.Length, e) &&
                                CheckSlotsSimple(0, toSlot, e)))
    }

    method getEmpty(e: int) returns (r: int)
        requires Valid();
        ensures Valid();
        ensures r < a.Length;
        ensures (r == -1) ==> CheckSlots(0, a.Length, Empty);
        ensures r >= 0 ==> CheckSlots(hash(e), r, Empty);
        ensures r < a.Length;
        ensures (r >= 0) ==> (a[r].Empty?);
    {
        var originalSlot := hash(e);
        var slotsChecked : nat := 0;
        var curSlot := originalSlot;

        while (slotsChecked < a.Length)
            invariant Valid();
            invariant slotsChecked <= a.Length;
            invariant slotsChecked + originalSlot <  a.Length ==> CheckSlotsSimple(originalSlot, slotsChecked + originalSlot, Empty);
            invariant slotsChecked + originalSlot >= a.Length ==> CheckSlotsSimple(0, (slotsChecked + originalSlot) - a.Length, Empty) &&
                CheckSlotsSimple(originalSlot, a.Length, Empty);
            decreases a.Length - slotsChecked;
        {
            curSlot := (originalSlot + slotsChecked) % a.Length;
            if (a[curSlot].Empty?)
            {
                r := curSlot;
                assert CheckSlots(hash(e), r, Empty);
                return;
            }
            slotsChecked := slotsChecked + 1;
        }
        r := -1;
    }

    function method hash(e: int) : int
        reads this, a;
        requires 0 < a.Length;
    {
        // (31 * (17 + e)) % a.Length
        e % a.Length
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