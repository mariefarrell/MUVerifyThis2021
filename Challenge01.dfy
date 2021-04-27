predicate sorted(s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

predicate reverseSorted(s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] >= s[j]
}

predicate sortedRange(s: seq<int>, l: int, u: int)
    requires 0 <= l <= u <= |s|
{
    sorted(s[l..u])
}

predicate reverseSortedRange(s: seq<int>, l: int, u: int)
    requires 0 <= l <= u <= |s|
{
    reverseSorted(s[l..u])
}


predicate lastPerm(s: seq<int>)
{
    reverseSorted(s)
}

predicate ltseq(a: seq<int>, b: seq<int>)
    requires |a| == |b|
{
    exists j | 0 <= j < |a| :: a[..j] == b[..j] && a[j] < b[j]
}

predicate strictlySortedSeq(S: seq<seq<int>>)
    requires forall i | 0 <= i < |S| - 1 :: |S[i]| == |S[i + 1]|
{
    |S| > 1 ==> forall i | 0 <= i < |S| - 1 :: ltseq(S[i], S[i + 1])
}

function method min(a: int, b: int): int
{
    if a < b then a else b
}

function method factorial(n: int): int
    requires n >= 0
    ensures factorial(n) > 0
    decreases n
{
    if n == 0 then 1 else n * factorial(n - 1)
}

function rankNat(rank: seq<int>): int
{
    if |rank| == 0 then 0 else
    rank[0] * factorial(|rank| - 1) + rankNat(rank[1..])
}

method next(a: array<int>) returns (ok: bool)
   modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))  
    ensures !ok ==> a[..] == old(a[..]) && lastPerm(a[..])  
    ensures ok  ==> ltseq(old(a[..]), a[..])  
{
    var len := a.Length;
    var i := len - 1;

    while i > 0 && a[i - 1] >= a[i]
        invariant -1 <= i < len
        invariant i >= 0 ==> reverseSortedRange(a[..], i, a.Length)
        invariant i == -1 ==> len == 0
        invariant a[..] == old(a[..])
        decreases i
    {
        i := i - 1;
    }

    if i <= 0 {
        ok := false;
        return;
    }

    var j := len - 1;

    while a[j] <= a[i - 1]
        invariant a[..] == old(a[..])
        invariant j > i - 1
        decreases j
    {
        j := j - 1;
    }

    a[i - 1], a[j] := a[j], a[i - 1];

    ghost var idx := min(i - 1, j);

    var k := i - 1;

    j := len - 1;
    while i < j
        invariant k < i < len
        invariant k <= j < len
        invariant a[..idx] == old(a[..idx])
        invariant a[idx] > old(a[idx])
        invariant old(multiset(a[..])) == multiset(a[..])
        decreases j - i
    {
        a[i], a[j] := a[j], a[i];
        i := i + 1;
        j := j - 1;
    }

    ok := true;
}

method {:verify false} sort(a: array<int>)
    modifies a
    ensures sorted(a[..])
    ensures |a[..]| == |old(a[..])|
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    
}

method permut(a: array<int>) returns (result: seq<seq<int>>)
    modifies a
    ensures forall i | 0 <= i < |result| - 1 :: |result[i]| == |result[i + 1]|
    ensures forall i | 1 <= i < |result| - 1 :: result[i] != result[i - 1]  
    ensures strictlySortedSeq(result)
{
    result := [];

    if a.Length <= 0 {
        return [[]];
    }

    sort(a);

    result := result + [a[..]];

    ghost var len := |a[..]|;

    var ok := next(a);
    var fac := factorial(a.Length); 
    
    while ok && fac > 0
        invariant |result| >= 1
        invariant forall i | 0 <= i < |result| :: |result[i]| == len
        invariant forall i | 0 <= i < |result| - 1 :: |result[i]| == |result[i + 1]|
        invariant ok ==> forall i | 0 <= i < |result| :: ltseq(result[i], a[..])
        invariant strictlySortedSeq(result)
        decreases fac 
        invariant forall i | 1 <= i < |result| - 1 :: result[i] != result[i-1]
    {
        result := result + [a[..]];
        ok := next(a);
        fac := fac - 1;

    }
}
