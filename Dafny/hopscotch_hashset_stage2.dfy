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
        // The array is valid
        ValidArray(a) &&
        // Exclusivity is maintained.
        Exclusivity() &&
        // Contents is maintained alongside the array
        (Contents == set x: int | 0 <= x < a.Length && a[x].Entry? :: a[x].i) &&
        // For all items in Contents...
        (forall e :: (e in Contents) ==>
                                         // The entry is in the probe chain
                                         (exists h :: h in getProbeChain(hash(e)) && a[h].Entry? && a[h].i == e) &&
                                         // The entry is not outside the probe chain
                                         (forall h :: h !in getProbeChain(hash(e)) && 0 <= h < a.Length && a[h].Entry? ==> a[h].i != e) &&
                                         // There is an item with a next offset of 0 in every probe chain
                                         (exists h :: h in getProbeChain(hash(e)) && 0 <= h < a.Length && a[h].nextOffset == 0)) &&
        // If the entry is empty, the probe chain starting at that point is empty, and there are no items in the array with a hash equal to that entry
        (forall i :: 0 <= i < a.Length &&  a[i].Empty? ==> getProbeChain(i) == {} && (forall j :: 0 <= j < a.Length && !a[j].Empty? ==> a[j].hash != i)) &&
        // All hashes are positive and less than the array length
        (forall i :: 0 <= i < a.Length && !a[i].Empty? ==> 0 <= a[i].hash < a.Length) &&
        // All offsets are positive and less than the array length
        (forall i :: 0 <= i < a.Length && !a[i].Empty? ==> 0 <= a[i].nextOffset < a.Length && 0 <= a[i].startOffset < a.Length) &&
        // For all items where the start offset is 0 but the hash of the entry at that slot is not equal to the slot, the probe chain for that slot is empty
        (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].hash != i && a[i].startOffset == 0 ==> getProbeChain(i) == {}) &&
        // For all items where the start offset is greater than 0, there is no entry with the same hash between the hash location and that location
        (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].startOffset > 0 ==>
            (i <= (i+a[i].startOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
            (i > (i+a[i].startOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                    (forall x :: 0 < x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)))) &&
        // For all non-empty items where the start offset slot has no next offset, the probe chain consists only of the first item
        (forall i :: 0 <= i < a.Length && !a[i].Empty? && !a[(i+a[i].startOffset)%a.Length].Empty? && a[(i+a[i].startOffset)%a.Length].hash == i
            && a[(i+a[i].startOffset)%a.Length].nextOffset == 0 ==> getProbeChain(i) == {(i+a[i].startOffset)%a.Length}) &&
        // For all items where the next offset is greater than 0, there is no entry with the same hash between the hash location and that location
        (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset > 0 ==>
            (i <= (i+a[i].nextOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
            (i > (i+a[i].nextOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                   (forall x :: 0 <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)))) &&
        // For all items where the next offset is 0, there is no entry with the same hash between that location and the hash location
        (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset == 0 ==>
            (i <= a[i].hash ==> (forall x :: i < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
            (i > a[i].hash ==> (forall x :: i < x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                               (forall x :: 0 < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash))) &&
        // For all items where the next offset is greater than 0, the distance from the next offset to the hash is less than the distance from the current slot to hash
        (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset > 0 ==>
            distance((i+a[i].nextOffset)%a.Length,a[i].hash) < distance(i, a[i].hash))
    }

    function getProbeChain(h: int) : set<int>
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
        var bucket := hash(e);
        ghost var probeChain := getProbeChain(bucket);
        ghost var indexesToCheck := getProbeChain(bucket);
        ghost var indexesChecked : set<int> := {};

        if(a[bucket].Empty?){
            assert Valid();
            assert {} == getProbeChain(bucket);
            a[bucket] := Entry(e, bucket, 0, 0);
            Contents := Contents + {e};
            assert {bucket} == getProbeChain(bucket);
            
            assert a[bucket].i == e;
            assert e in Contents;
            assert forall j: int :: 0 <= j < a.Length && j != bucket ==> a[j] == old(a[j]);
            assert Contents == old(Contents) + {e};
            
            assert (Contents == set x: int | 0 <= x < a.Length && a[x].Entry? :: a[x].i);
            assert (forall e :: (e in Contents) ==>
                                         (exists h :: h in getProbeChain(hash(e)) && a[h].Entry? && a[h].i == e) &&
                                         (forall h :: h !in getProbeChain(hash(e)) && 0 <= h < a.Length && a[h].Entry? ==> a[h].i != e) &&
                                         (exists h :: h in getProbeChain(hash(e)) && 0 <= h < a.Length && a[h].nextOffset == 0));
            assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && !a[(i+a[i].startOffset)%a.Length].Empty? && a[(i+a[i].startOffset)%a.Length].hash == i
                && a[(i+a[i].startOffset)%a.Length].nextOffset == 0 ==> getProbeChain(i) == {(i+a[i].startOffset)%a.Length});
            assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].startOffset > 0 ==>
                (i <= (i+a[i].startOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                (i > (i+a[i].startOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                        (forall x :: 0 < x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash))));
            assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset > 0 ==>
                (i <= (i+a[i].nextOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                (i > (i+a[i].nextOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                    (forall x :: 0 <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash))));
            assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset > 0 ==>
                distance((i+a[i].nextOffset)%a.Length,a[i].hash) < distance(i, a[i].hash));
            assert Valid();

            assert Contents == old(Contents) + {e};
            r := true;
            return;
        }

        var start := (bucket + a[bucket].startOffset) % a.Length;
        var curr := start;
        assert indexesChecked + indexesToCheck == probeChain;

        if(a[bucket].hash != bucket && a[bucket].startOffset == 0){
            assert indexesToCheck == {};
            assert e !in Contents;
        }
        else {
            assert a[start].hash == bucket;

            if(a[curr].Entry? && a[curr].i == e){
                r := true;

                assert r == (e in Contents);
                return;
            }
            indexesChecked := indexesChecked + {curr};
            indexesToCheck := indexesToCheck - {curr};

            assert !a[bucket].Empty?;
            assert !a[curr].Empty?;
            assert a[curr].hash == bucket;
            assert (!a[bucket].Empty? && !a[curr].Empty? && a[curr].hash == bucket
                && a[curr].nextOffset == 0 ==> probeChain == {curr});
            
            assert a[curr].nextOffset == 0 ==> probeChain == {curr};

            while(a[curr].nextOffset != 0)
                invariant Valid();
                invariant 0 <= curr < a.Length;
                invariant !a[curr].Empty?;
                invariant a[curr].hash == bucket;
                invariant forall i :: i in probeChain ==> 0 <= i < a.Length;
                invariant forall i :: i in indexesToCheck ==> 0 <= i < a.Length;
                invariant forall i :: i in indexesChecked ==> 0 <= i < a.Length;
                invariant forall i :: i in indexesChecked && a[i].Entry? ==> a[i].i != e;
                invariant indexesToCheck <= probeChain;
                invariant indexesChecked <= probeChain;
                invariant curr in probeChain;
                invariant curr !in indexesToCheck;
                invariant curr in indexesChecked;
                invariant indexesChecked !! indexesToCheck;
                invariant probeChain == getProbeChain(bucket);
                invariant indexesChecked + indexesToCheck == probeChain;
                invariant forall i :: i in indexesToCheck ==> 0 <= i < a.Length && !a[i].Empty? && a[i].hash == bucket;
                invariant forall x :: 0 <= x < a.Length && !a[x].Empty? && a[x].hash == bucket ==>
                    (x in indexesToCheck && x !in indexesChecked) || (x !in indexesToCheck && x in indexesChecked);
                decreases |indexesToCheck|;
            {
                curr := (curr + a[curr].nextOffset) % a.Length;
                indexesChecked := indexesChecked + {curr};
                indexesToCheck := indexesToCheck - {curr};
                if(a[curr].Entry? && a[curr].i == e){
                    r := true;
                    return;
                }
            }
            assert |indexesToCheck| == 0;
            assert indexesToCheck == {};
            assert indexesChecked == probeChain;
            assert e !in Contents;
        }

        // Linear probing
        var lastSlot := curr;
        var slotsChecked : nat := 0;
        var curSlot := curr;
        assert !a[lastSlot].Empty?;

        var slotsLeftToCheck := distance(curSlot, bucket);

        assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset == 0 ==>
                (i <= a[i].hash ==> (forall x :: i < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                (i > a[i].hash ==> (forall x :: i < x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                (forall x :: 0 < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)));

        assert 0 <= lastSlot < a.Length && !a[lastSlot].Empty? && a[lastSlot].nextOffset == 0;

        assert (lastSlot <= bucket ==> (forall x :: lastSlot < x < bucket && !a[x].Empty? ==> bucket != a[x].hash)) &&
                (lastSlot > bucket ==> (forall x :: lastSlot < x < a.Length && !a[x].Empty? ==> bucket != a[x].hash) && // HERE
                                (forall x :: 0 < x < bucket && !a[x].Empty? ==> bucket != a[x].hash)); 

        while (slotsChecked < slotsLeftToCheck)
            invariant Valid();
            invariant slotsChecked <= slotsLeftToCheck;
            invariant 0 <= lastSlot < a.Length;
            invariant 0 <= curSlot < a.Length;
            invariant (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset == 0 ==>
                (i <= a[i].hash ==> (forall x :: i < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                (i > a[i].hash ==> (forall x :: i < x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                (forall x :: 0 < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)));
            invariant (lastSlot <= bucket ==> (forall x :: lastSlot < x < bucket && !a[x].Empty? ==> bucket != a[x].hash)) &&
                      (lastSlot > bucket ==> (forall x :: lastSlot < x < a.Length && !a[x].Empty? ==> bucket != a[x].hash) &&
                                (forall x :: 0 < x < bucket && !a[x].Empty? ==> bucket != a[x].hash));
            invariant (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset > 0 ==>
                    (i <= (i+a[i].nextOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                    (i > (i+a[i].nextOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                        (forall x :: 0 <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash))));
            invariant (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].startOffset > 0 ==>
                    (i <= (i+a[i].startOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                    (i > (i+a[i].startOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                            (forall x :: 0 < x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash))));
            invariant (forall i :: 0 <= i < a.Length && !a[i].Empty? && !a[(i+a[i].startOffset)%a.Length].Empty? && a[(i+a[i].startOffset)%a.Length].hash == i
                    && a[(i+a[i].startOffset)%a.Length].nextOffset == 0 ==> getProbeChain(i) == {(i+a[i].startOffset)%a.Length});
            decreases a.Length - slotsChecked;
        {
            curSlot := (lastSlot + slotsChecked) % a.Length;

            if (a[curSlot].Empty?)
            {
                assert lastSlot != curSlot;
                a[curSlot] := Entry(e, bucket, 0, 0);
                Contents := Contents + {e};
                assert !a[lastSlot].Empty?;
                var isFirst := (lastSlot == bucket && a[lastSlot].hash != bucket && a[bucket].startOffset == 0);
                var dist := distance(lastSlot, curSlot);
                if(isFirst){
                    if(a[lastSlot].Entry?){
                        a[lastSlot] := Entry(a[lastSlot].i, a[lastSlot].hash, dist, a[lastSlot].nextOffset);
                        assert a[lastSlot].i == old(a[lastSlot]).i;
                    }
                    else {
                        a[lastSlot] := Tombstone(a[lastSlot].hash, dist, a[lastSlot].nextOffset);
                    }
                    assert bucket == lastSlot;
                    assert a[lastSlot].hash == old(a[lastSlot]).hash;
                    assert a[lastSlot].nextOffset == old(a[lastSlot]).nextOffset;
                    assert a[lastSlot].startOffset == dist;
                    assert a[bucket].hash != bucket ==> a[bucket].startOffset > 0;
                }
                else {
                    if(a[lastSlot].Entry?){
                        a[lastSlot] := Entry(a[lastSlot].i, a[lastSlot].hash, a[lastSlot].startOffset, dist);
                        assert a[lastSlot].i == old(a[lastSlot]).i;
                    }
                    else{
                        a[lastSlot] := Tombstone(a[lastSlot].hash, a[lastSlot].startOffset, dist);
                    }
                    assert a[lastSlot].hash == old(a[lastSlot]).hash;
                    assert a[lastSlot].startOffset == old(a[lastSlot]).startOffset;
                    assert a[lastSlot].nextOffset == dist;
                }
                assert old(a)[lastSlot].Entry? ==> a[lastSlot].Entry?;
                assert a[lastSlot].Entry? ==> a[lastSlot].i == old(a)[lastSlot].i;
                assert forall j: int :: 0 <= j < a.Length && j != curSlot && j != lastSlot ==> a[j] == old(a[j]);

                assert !a[bucket].Empty?;
                assert !a[lastSlot].Empty?;
                assert a[curSlot].i == e;
                assert a[curSlot].hash == bucket;
                assert a[curSlot].nextOffset == 0;
                assert a[curSlot].startOffset == 0;
                assert forall j: int :: 0 <= j < a.Length && j != curSlot && j != lastSlot ==> a[j] == old(a[j]);
                assert forall j: int :: 0 <= j < a.Length && j != curSlot && a[j].Entry? ==> a[j].i == old(a[j]).i;
                assert forall j: int :: 0 <= j < a.Length && !a[j].Empty? && !old(a[j]).Empty? ==> a[j].hash == old(a[j]).hash;
                assert forall j: int :: 0 <= j < a.Length && j != lastSlot && !a[j].Empty? && !old(a[j]).Empty? ==> a[j].startOffset == old(a[j]).startOffset;
                assert forall j: int :: 0 <= j < a.Length && j != lastSlot && !a[j].Empty? && !old(a[j]).Empty? ==> a[j].nextOffset == old(a[j]).nextOffset;
                assert forall j: int :: 0 <= j < a.Length && j != bucket ==> getProbeChain(j) == old(getProbeChain(j));
                assert getProbeChain(bucket) == probeChain + {curSlot};

                r := true;

                assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset > 0 ==> // HERE
                    (i < (i+a[i].nextOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                    (i > (i+a[i].nextOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                        (forall x :: 0 <= x < (i+a[i].nextOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash))));
                assert a[bucket].hash != bucket ==> a[bucket].startOffset > 0; // HERE

                assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].hash != i && a[i].startOffset == 0 ==> getProbeChain(i) == {});
                assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].startOffset > 0 ==> // HERE
                    (i < (i+a[i].startOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                    (i > (i+a[i].startOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                            (forall x :: 0 < x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash))));
                assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset > 0 ==>
                    distance((i+a[i].nextOffset)%a.Length,a[i].hash) < distance(i, a[i].hash));
                assert (forall e :: (e in Contents) ==>
                                         (exists h :: h in getProbeChain(hash(e)) && a[h].Entry? && a[h].i == e) &&
                                         (forall h :: h !in getProbeChain(hash(e)) && 0 <= h < a.Length && a[h].Entry? ==> a[h].i != e) &&
                                         (exists h :: h in getProbeChain(hash(e)) && 0 <= h < a.Length && a[h].nextOffset == 0));
                assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset == 0 ==>
                    (i < a[i].hash ==> (forall x :: i < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                    (i > a[i].hash ==> (forall x :: i < x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                    (forall x :: 0 < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)));
                assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && !a[(i+a[i].startOffset)%a.Length].Empty? && a[(i+a[i].startOffset)%a.Length].hash == i
                    && a[(i+a[i].startOffset)%a.Length].nextOffset == 0 ==> getProbeChain(i) == {(i+a[i].startOffset)%a.Length}); 

                assert Valid();
                return;
            }
            
            assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].nextOffset == 0 ==>
                (i < a[i].hash ==> (forall x :: i < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                (i > a[i].hash ==> (forall x :: i < x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                (forall x :: 0 < x < a[i].hash && !a[x].Empty? ==> a[i].hash != a[x].hash)));

            assert a[curSlot].hash != bucket; // HERE

            slotsChecked := slotsChecked + 1;
        }
        r := false;
    }

    method remove(e: int) returns (r: bool)
        ensures a == old(a);
        ensures r == (e in old(Contents))
        ensures Contents == old(Contents) - {e};
        ensures forall j: int :: 0 <= j < a.Length && a[j].Entry? ==> a[j].i != e;
    {
        var bucket := hash(e);
        ghost var probeChain := getProbeChain(bucket);
        ghost var indexesToCheck := getProbeChain(bucket);
        ghost var indexesChecked : set<int> := {};

        if(a[bucket].Empty?){
            assert indexesToCheck == {};
            r := false;
            return;
        }

        if(a[bucket].hash != bucket && a[bucket].startOffset == 0){
            assert indexesToCheck == {};
            assert e !in Contents;
            r := false;
            return;
        }

        var start := (bucket + a[bucket].startOffset) % a.Length;
        assert !a[start].Empty?;

        if(a[start].Entry? && a[start].i == e){
            a[start] := Tombstone(a[start].hash, a[start].startOffset, a[start].nextOffset);
            Contents := Contents - {e};
            r := true;
            assert !a[start].Entry?;
            assert forall i :: 0 <= i < a.Length && i != start ==> a[i] == old(a[i]);
            assert (Contents == set x: int | 0 <= x < a.Length && a[x].Entry? :: a[x].i);
            assert forall i :: 0 <= i < a.Length && !a[i].Empty? && a[i].startOffset > 0 ==>
                (i < (i+a[i].startOffset)%a.Length ==>  (forall x :: i <= x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)) &&
                (i > (i+a[i].startOffset)%a.Length ==> ((forall x :: i <= x < a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash) &&
                                                        (forall x :: 0 < x < (i+a[i].startOffset)%a.Length && !a[x].Empty? ==> a[i].hash != a[x].hash)));
            assert (forall i :: 0 <= i < a.Length && !a[i].Empty? && !a[(i+a[i].startOffset)%a.Length].Empty? && a[(i+a[i].startOffset)%a.Length].hash == i
                && a[(i+a[i].startOffset)%a.Length].nextOffset == 0 ==> getProbeChain(i) == {(i+a[i].startOffset)%a.Length});
            assert Valid();
            return;
        }

        var curr := start;
        assert indexesChecked + indexesToCheck == probeChain;

        indexesChecked := indexesChecked + {curr};
        indexesToCheck := indexesToCheck - {curr};

        assert !a[bucket].Empty?;
        assert !a[curr].Empty?;
        assert a[curr].hash == bucket;
        assert (!a[bucket].Empty? && !a[curr].Empty? && a[curr].hash == bucket
            && a[curr].nextOffset == 0 ==> probeChain == {curr});

        assert a[curr].nextOffset == 0 ==> probeChain == {curr};

        while(a[curr].nextOffset != 0)
            invariant Valid();
            invariant 0 <= curr < a.Length;
            invariant !a[curr].Empty?;
            invariant a[curr].hash == bucket;
            invariant forall i :: i in probeChain ==> 0 <= i < a.Length;
            invariant forall i :: i in indexesToCheck ==> 0 <= i < a.Length;
            invariant forall i :: i in indexesChecked ==> 0 <= i < a.Length;
            invariant forall i :: i in indexesChecked && a[i].Entry? ==> a[i].i != e;
            invariant indexesToCheck <= probeChain;
            invariant indexesChecked <= probeChain;
            invariant curr in probeChain;
            invariant curr !in indexesToCheck;
            invariant curr in indexesChecked;
            invariant indexesChecked !! indexesToCheck;
            invariant probeChain == getProbeChain(bucket);
            invariant indexesChecked + indexesToCheck == probeChain;
            invariant forall i :: i in indexesToCheck ==> 0 <= i < a.Length && !a[i].Empty? && a[i].hash == bucket;
            invariant forall x :: 0 <= x < a.Length && !a[x].Empty? && a[x].hash == bucket ==>
                (x in indexesToCheck && x !in indexesChecked) || (x !in indexesToCheck && x in indexesChecked);
            decreases |indexesToCheck|;
        {
            curr := (curr + a[curr].nextOffset) % a.Length;
            indexesChecked := indexesChecked + {curr};
            indexesToCheck := indexesToCheck - {curr};
            if(a[curr].Entry? && a[curr].i == e){
                a[start] := Tombstone(a[start].hash, a[start].startOffset, a[start].nextOffset);
                Contents := Contents - {e};
                r := true;
                return;
            }
        }
        r := false;
        assert |indexesToCheck| == 0;
        assert indexesToCheck == {};
        assert indexesChecked == probeChain;
        assert e !in Contents;
    }

    method get(e: int) returns (r: int)
        ensures r < a.Length;
        ensures (r >= 0) ==> (a[r].Entry? && a[r].i == e);
        ensures (r >= 0) ==> (forall j: int :: 0 <= j < a.Length && j != r && a[j].Entry? ==> a[j].i != e);
        ensures (r == -1) ==> (forall h :: h in getProbeChain(hash(e)) && a[h].Entry? ==> a[h].i != e)
    {
        var hash := hash(e);
        ghost var probeChain := getProbeChain(hash);
        ghost var indexesToCheck := getProbeChain(hash);
        ghost var indexesChecked : set<int> := {};

        if(a[hash].Empty?){
            assert indexesToCheck == {};
            r := -1;
            return;
        }

        if(a[hash].hash != hash && a[hash].startOffset == 0){
            assert indexesToCheck == {};
            assert e !in Contents;
            r := -1;
            return;
        }

        var start := (hash + a[hash].startOffset) % a.Length;
        assert !a[start].Empty?;

        if(a[start].Entry? && a[start].i == e){
            r := start;
            assert (r >= 0) ==> (a[r].Entry? && a[r].i == e);
            return;
        }

        var curr := start;
        assert indexesChecked + indexesToCheck == probeChain;

        indexesChecked := indexesChecked + {curr};
        indexesToCheck := indexesToCheck - {curr};

        assert (!a[hash].Empty? && !a[(hash+a[hash].startOffset)%a.Length].Empty? && a[(hash+a[hash].startOffset)%a.Length].hash == hash
            && a[(hash+a[hash].startOffset)%a.Length].nextOffset == 0 ==> getProbeChain(hash) == {(hash+a[hash].startOffset)%a.Length});

        assert a[curr].nextOffset == 0 ==> probeChain == {curr};

        while(a[curr].nextOffset != 0)
            invariant Valid();
            invariant 0 <= curr < a.Length;
            invariant !a[curr].Empty?;
            invariant a[curr].hash == hash;
            invariant forall i :: i in probeChain ==> 0 <= i < a.Length;
            invariant forall i :: i in indexesToCheck ==> 0 <= i < a.Length;
            invariant forall i :: i in indexesChecked ==> 0 <= i < a.Length;
            invariant forall i :: i in indexesChecked && a[i].Entry? ==> a[i].i != e;
            invariant indexesToCheck <= probeChain;
            invariant indexesChecked <= probeChain;
            invariant curr in probeChain;
            invariant curr !in indexesToCheck;
            invariant curr in indexesChecked;
            invariant indexesChecked !! indexesToCheck;
            invariant probeChain == getProbeChain(hash);
            invariant indexesChecked + indexesToCheck == probeChain;
            invariant forall i :: i in indexesToCheck ==> 0 <= i < a.Length && !a[i].Empty? && a[i].hash == hash;
            invariant forall x :: 0 <= x < a.Length && !a[x].Empty? && a[x].hash == hash ==>
                (x in indexesToCheck && x !in indexesChecked) || (x !in indexesToCheck && x in indexesChecked);
            decreases |indexesToCheck|;
        {
            curr := (curr + a[curr].nextOffset) % a.Length;
            indexesChecked := indexesChecked + {curr};
            indexesToCheck := indexesToCheck - {curr};
            if(a[curr].Entry? && a[curr].i == e){
                r := curr;
                return;
            }
        }
        r := -1;
        assert |indexesToCheck| == 0;
        assert indexesToCheck == {};
        assert indexesChecked == probeChain;
        assert e !in Contents;
    }

    function method distance(slotFrom: int, slotTo: int) : int
        reads this, Repr, a;
        requires ValidArray(a);
        ensures 0 <= distance(slotFrom, slotTo) < a.Length;
        ensures (slotFrom + distance(slotFrom, slotTo)) % a.Length == slotTo;

    function method hash(e: int) : int
        reads this, a;
        requires 0 < a.Length;
    {
        // (31 * (17 + e)) % a.Length
        e % a.Length
    }
  }
}