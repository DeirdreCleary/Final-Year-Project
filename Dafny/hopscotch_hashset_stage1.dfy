include "hashset_interface.dfy"

module HopscotchHashset refines HashsetInterface{
  datatype Item = Empty | Entry(i: int, hash: int, startOffset: int, nextOffset: int) | Tombstone(hash: int, startOffset: int, nextOffset: int)
    
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
        (forall e :: e in Contents ==> (exists h :: h in getIndexes(hash(e)) && a[h].Entry? && a[h].i == e)) &&
        (forall e :: e in Contents ==> (forall h :: 0 <= h < a.Length && h !in getIndexes(hash(e)) && a[h].Entry? ==> a[h].i != e)) &&
        (forall i :: 0 <= i < a.Length ==> (forall h :: h in getIndexes(i) && a[h].Entry? ==> a[h].i in Contents))
    }

    function method getIndexes(h: int) : set<int>
        reads this, Repr;
        requires ValidArray(a);
    {
        set x: int | 0 <= x < a.Length && !a[x].Empty? && a[x].hash == h :: x
    }

    predicate Exclusivity()
        reads this, a;
    {
        forall i: int, j: int :: 0 <= i < a.Length && 0 <= j < a.Length && j != i && a[i].Entry? && a[j].Entry?
             ==> a[i].i != a[j].i
    }

    constructor (size: int)
        ensures fresh(a);
        ensures Repr == {a};
        ensures 0 < a.Length;
    {
        a := new Item[size](_ => Empty);
        Contents := {};
        Repr := {a};
    }

    method insert(e: int) returns (r: bool)
        ensures a == old(a);
        ensures !r == (Contents == old(Contents)
            && forall j: int :: 0 <= j < a.Length && a[j].Entry? ==> a[j].i != e);
        ensures r == (Contents == old(Contents) + {e}
            && exists j: int :: 0 <= j < a.Length && a[j].Entry? && a[j].i == e);
    {
        var index := get(e);
        var bucket := hash(e);
        if(index > -1){
            assert Contents == old(Contents);
            r := true;
        }
        else{
            var firstEmpty, lastSlot := getEmpty(bucket);
            var isFirst := a[lastSlot].Empty? || (lastSlot == bucket && a[lastSlot].hash != bucket && a[bucket].startOffset == 0);
            if(firstEmpty > -1){
                a[firstEmpty] := Entry(e, bucket, 0, 0);
                Contents := Contents + {e};
                assert a[firstEmpty].Entry? && a[firstEmpty].i == e;
                assert forall j: int :: 0 <= j < a.Length && j != firstEmpty ==> a[j] == old(a[j]);
                assert (Contents == set x: int | 0 <= x < a.Length && a[x].Entry? :: a[x].i);
                assert Valid();

                if(isFirst){
                    if(a[lastSlot].Entry?){
                        a[lastSlot] := Entry(a[lastSlot].i, a[lastSlot].hash, distance(lastSlot, firstEmpty), a[lastSlot].nextOffset);
                    }
                    if(a[lastSlot].Tombstone?){
                        a[lastSlot] := Tombstone(a[lastSlot].hash, distance(lastSlot, firstEmpty), a[lastSlot].nextOffset);
                    }
                }
                else {
                    if(a[lastSlot].Entry?){
                        a[lastSlot] := Entry(a[lastSlot].i, a[lastSlot].hash, a[lastSlot].startOffset, distance(lastSlot, firstEmpty));
                    }
                    if(a[lastSlot].Tombstone?){
                        a[lastSlot] := Tombstone(a[lastSlot].hash, a[lastSlot].startOffset, distance(lastSlot, firstEmpty));
                    }
                }
                assert old(a)[lastSlot].Entry? ==> a[lastSlot].Entry?;
                assert a[lastSlot].Entry? ==> a[lastSlot].i == old(a)[lastSlot].i;
                assert forall j: int :: 0 <= j < a.Length && j != firstEmpty && j != lastSlot ==> a[j] == old(a[j]);
                assert forall j: int :: 0 <= j < a.Length && j != firstEmpty && a[j].Entry? ==> a[j].i == old(a[j]).i;
                
                r := true;
            }
            else{
                r := false;
            }
        }
    }
    
    method remove(e: int) returns (r: bool)
        ensures a == old(a);
        ensures r == (e in old(Contents))
        ensures Contents == old(Contents) - {e};
        ensures forall j: int :: 0 <= j < a.Length && a[j].Entry? ==> a[j].i != e;
    {
        var index := get(e);
        var bucket := hash(e);
        if(index <= -1){
            r := false;
        }
        else{
            a[index] := Tombstone(a[index].hash, a[index].startOffset, a[index].nextOffset);
            Contents := Contents - {e};
            assert forall i :: 0 <= i < a.Length && i != index ==> a[i] == old(a[i]);
            assert Exclusivity();
            assert (forall e :: e in Contents ==> (forall h :: h !in getIndexes(hash(e)) && 0 <= h < a.Length && a[h].Entry? ==> a[h].i != e));

            r := true;
        }
    }

    method get(e: int) returns (r: int)
        ensures r < a.Length;
        ensures (r >= 0) ==> (a[r].Entry? && a[r].i == e);
        ensures (r >= 0) ==> (forall j: int :: 0 <= j < a.Length && j != r && a[j].Entry? ==> a[j].i != e);
    {
        var indexesToCheck := getIndexes(hash(e));
        
        var beginSlot := 0;
        while(beginSlot < a.Length)
            invariant beginSlot <= a.Length;
            invariant forall i :: 0 <= i < beginSlot <= a.Length && a[i].Entry? ==> a[i].i != e;
            decreases a.Length - beginSlot;
        {
            if(beginSlot in indexesToCheck && a[beginSlot].Entry? && a[beginSlot].i == e){
                r := beginSlot;
                return;
            }
            beginSlot := beginSlot + 1;
        }

        r := -1;

        return;
    }

    method getEmpty(startPos: int) returns (r: int, lastSlot: int)
        requires Valid();
        requires 0 <= startPos < a.Length;
        ensures 0 <= lastSlot < a.Length;
        ensures r < a.Length;
        ensures (r >= 0) ==> (a[r].Empty?);
        ensures a == old(a);
        ensures Valid();
    {
        var indexesToCheck := getIndexes(startPos);
        var beginSlot := 0;
        var longestDistance := a.Length;
        lastSlot := startPos;

        while(beginSlot < a.Length)
            invariant lastSlot < a.Length;
            decreases a.Length - beginSlot;
        {
            if(beginSlot in indexesToCheck){
                var dist := distance(startPos, beginSlot);
                if(longestDistance > dist){
                    lastSlot := beginSlot;
                    longestDistance := dist;
                }
            }
            assert lastSlot < a.Length;
            beginSlot := beginSlot + 1;
        }
        
        var dist := distance(startPos, lastSlot);
        var probeOffset := 0;

        while((a.Length - dist) - probeOffset > 0)
            decreases (a.Length - dist) - probeOffset;
        {
            if(a[(lastSlot + probeOffset) % a.Length].Empty?){
                r := (lastSlot + probeOffset) % a.Length;
                return;
            }
            probeOffset := probeOffset + 1;
        }

        r := -1;
    }

    predicate checkSlotsForEmpty(fromSlot: int, toSlot: int)
        reads this, a;
        requires a.Length > 0;
    {
        (toSlot >= fromSlot ==> ( forall k :: 0 <= fromSlot <= k < toSlot < a.Length   ==> !a[k].Empty?)) &&
        (toSlot <  fromSlot ==> ((forall k :: 0 <= fromSlot <= k < a.Length ==> !a[k].Empty?)  && 
                                 (forall k :: 0 <= k < toSlot < a.Length    ==> !a[k].Empty?)))
    }

    function method distance(slotFrom: int, slotTo: int) : int
        reads this, Repr, a;
        requires Valid();
    {
        if (slotTo < slotFrom) then (a.Length - slotFrom + slotTo) else (slotTo - slotFrom)
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