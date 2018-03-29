module HashsetInterface{
    class Hashset{
        ghost var Contents: set<int>;
        ghost var Repr: set<object>;

        predicate Valid()
            reads Repr, this;

        constructor (size: int)
            requires size > 0;
            ensures Valid();
            ensures fresh(Repr);

        method insert(e: int) returns (r: bool)
            modifies Repr, this;
            requires Valid();
            ensures Valid();
            ensures Repr == old(Repr);
            ensures !r ==> Contents == old(Contents);
            ensures r ==> Contents == old(Contents) + {e};
            ensures r == (e in Contents);

        method remove(e: int) returns (r: bool)
            modifies Repr, this;
            requires Valid();
            ensures Valid();
            ensures Repr == old(Repr);
            ensures Contents == old(Contents) - {e};
            ensures r == (e in old(Contents));

        method get(e: int) returns (r: int)
            requires Valid();
            ensures Valid();
            ensures Repr == old(Repr);
            ensures (r >= 0) == (e in Contents);
            ensures (r == -1) == (e !in Contents);
    }
}