predicate sorted(s: seq<int>, l: nat, u: nat)
    requires 0 <= l <= u <= |s|
{
    forall i, j | l <= i < j < u :: s[i] <= s[j]
}

class Ref {
    var data: int
    var next: Ref?
    var prev: Ref?

    ghost var Repr: set<object>
    ghost var Contents: seq<int>

    constructor(data: int)
        ensures ValidLL()
        ensures ValidBST()
        ensures SortedLL()
    {
        this.data := data;
        next := null;
        prev := null;

        Repr := {this};
        Contents := [data];
    }

    predicate ValidRef()
        reads this, Repr
        decreases Repr
    {
        this in Repr &&
        |Contents| >= 1 && Contents[0] == data &&
        (prev != null ==>
            prev in Repr &&
            prev.Repr <= Repr &&
            this !in prev.Repr &&
            prev.ValidRef()) &&
        (next != null ==>
            next in Repr &&
            next.Repr <= Repr &&
            this !in next.Repr &&
            next.ValidRef()) &&
        (prev == null && next == null ==>
            Contents == [data]) &&
        (prev != null && next == null ==>
            Contents == prev.Contents + [data]) &&
        (prev == null && next != null ==>
            Contents == [data] + next.Contents) &&
        (prev != null && next != null ==>
            prev.Repr !! next.Repr &&
            Contents == prev.Contents + [data] + next.Contents)
    }

    predicate ValidLL()
        reads this, Repr
        decreases Repr
    {
        this in Repr &&
        |Contents| >= 1 && Contents[0] == data &&
        prev == null &&
        (next != null ==>
            next in Repr &&
            next.Repr <= Repr &&
            this !in next.Repr &&
            next.ValidLL() &&
            Contents == [data] + next.Contents) &&
        (next == null ==>
            Contents == [data])
    }

    predicate BalancedBST()
        reads this, Repr
        decreases Repr
        requires ValidBST()
    {
        ValidBSTisValidRef();
        (depth(next) == depth(prev) ||
            depth(next) == depth(prev) + 1 ||
            depth(next) + 1 == depth(prev)) &&
        (next != null ==> next.BalancedBST()) &&
        (prev != null ==> prev.BalancedBST())
    }

    lemma {:induction this} ValidLLisValidRef()
        requires ValidLL()
        ensures ValidRef()
        decreases this.Repr
    {
        if this.next != null && this.prev == null {
            this.next.ValidLLisValidRef();
        }
    }

    lemma {:induction this} ValidBSTisValidRef()
        requires ValidBST()
        ensures ValidRef()
        decreases this.Repr
    {
        if this.next != null && this.prev == null {
            this.next.ValidBSTisValidRef();
        }
    }

    predicate SortedLL()
        reads this, Repr
        requires ValidLL()
        decreases Repr
    {
        if next == null then true else
        if data <= next.data then next.SortedLL() else false
    }

    predicate ValidBST()
        reads this, Repr
        decreases Repr
    {
        this in Repr &&
        (prev != null ==>
            prev in Repr &&
            prev.Repr <= Repr &&
            this !in prev.Repr &&
            prev.ValidBST() &&
            forall x | x in prev.Contents :: x < data) &&
        (next != null ==>
            next in Repr &&
            next.Repr <= Repr &&
            this !in next.Repr &&
            next.ValidBST() &&
            forall x | x in next.Contents :: x > data) &&
        (prev == null && next == null ==>
            Contents == [data]) &&
        (prev != null && next == null ==>
            Contents == prev.Contents + [data]) &&
        (prev == null && next != null ==>
            Contents == [data] + next.Contents) &&
        (prev != null && next != null ==>
            prev.Repr !! next.Repr &&
            Contents == prev.Contents + [data] + next.Contents)
    }
}

function method max(a: int, b: int): int
{
    if a > b then a else b
}

function method depth(ref: Ref?): nat
    reads ref, if ref != null then ref.Repr else {}
    requires ref == null || ref.ValidRef()
    decreases if ref != null then ref.Repr else {}
{
    if ref == null then 0 else 1 + max(depth(ref.prev), depth(ref.next))
}

method stitchTree(ref: Ref, tree: Ref?)
    modifies ref
    requires ref.ValidLL()
    requires tree == null || tree.ValidBST()
{
    ref.prev := tree;
}

method size(ref: Ref?) returns (count: nat)
    requires ref == null || ref.ValidLL()

    ensures ref == null ==> count == 0
    ensures ref != null ==> count == |ref.Contents|
    decreases if ref != null then ref.Repr else {}
{
    if ref != null {
        count := size(ref.next);
        count := count + 1;
    } else {
        count := 0;
    }
}

method dll2bst(head: Ref?) returns (root: Ref?)
    modifies head, if head != null then head.Repr else {}
    requires head == null || (head.ValidLL() && head.SortedLL())
    ensures root == null || root.ValidBST()
{
    var n := size(head);
    var right: Ref?;
    root, right := dll2bstrec(head, n);
}

method dll2bstrec(head: Ref?, n: nat) returns (root: Ref?, right: Ref?)
    modifies head, if head != null then head.Repr else {}
    requires head == null || (head.ValidRef() && head.ValidLL() && head.SortedLL())
    ensures root == null || (root.ValidRef() && root.ValidBST())
    ensures right == null || (right.ValidRef() && right.ValidLL())
    ensures head != null ==>
        (n == |head.Contents| ==> right == null &&
        n < |head.Contents| ==> right != null)
    decreases n
{
    if n > 0 {
        var left: Ref?;
        left, root := dll2bstrec(head, n/2);
        assert left == null || left.ValidBST();
        assert root == null || root.ValidLL();
        assert root != null;
        assert root.ValidLL();
        root.prev := left;

        var temp: Ref?;
        temp, right := dll2bstrec(root.next, n - n/2 - 1);
        root.next := temp;
    } else {
        assert n == 0;
        root := null;
        right := head;
    }
}
