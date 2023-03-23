// Ch. 10: Datatype Invariants

module PQueue {
    export
        // Impl
        provides PQueue
        provides Empty, IsEmpty, Insert, RemoveMin
        // Spec
        provides Valid, Elements, EmptyCorrect, IsEmptyCorrect
        provides InsertCorrect, RemoveMinCorrect
        reveals IsMin

    // Implementation
    type PQueue = BraunTree
    datatype BraunTree =
        | Leaf
        | Node(x: int, left: BraunTree, right: BraunTree)

    function Empty(): PQueue {
        Leaf
    }

    predicate IsEmpty(pq: PQueue) {
        pq == Leaf
    }

    function Insert(pq: PQueue, y: int): PQueue {
        match pq
        case Leaf => Node(y, Leaf, Leaf)
        case Node(x, left, right) =>
            if y < x then
                Node(y, Insert(right ,x), left)
            else
                Node(x, Insert(right, y), left)
    }

    function RemoveMin(pq: PQueue): (int, PQueue)
      requires !IsEmpty(pq)
    {
        var Node(x, left, right) := pq;
        (x, DeleteMin(pq))
    }
    
    function DeleteMin(pq: PQueue): PQueue
      requires !IsEmpty(pq)
    // TODO
    /* { */
    /*     var pq' := match (left, right) */
    /*         case (Leaf, Leaf) => Leaf */
    /*         case (Leaf, Node(_, _, _)) => right */
    /*         case (Node(_, _, _), Leaf) => left */
    /*         case (Node(y1, left1, right1), Node(y2, left2, right2)) => */
    /*             if y1 < y2 then */
    /*                  */
    /* } */

    // Specification
    ghost function Elements(pq: PQueue): multiset<int> {
        match pq
        case Leaf => multiset{}
        case Node(x, left, right) =>
            multiset{x} + Elements(left) + Elements(right)
    }
    ghost predicate Valid(pq: PQueue) {
        IsBinaryHeap(pq) && IsBalanced(pq)
    }
    
    ghost predicate IsBinaryHeap(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(x, left, right) =>
            IsBinaryHeap(left) && IsBinaryHeap(right) &&
            (left.Leaf? || x <= left.x) &&
            (right.Leaf? || x <= right.x)
    }

    ghost predicate IsBalanced(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(_, left, right) =>
            IsBalanced(left) && IsBalanced(right) &&
            var L, R := |Elements(left)|, |Elements(right)|;
            L == R || L == R + 1
    }

    // Ex. 10.2
    lemma {:induction false} BinaryHeapStoresMin(pq: PQueue, y: int)
      requires IsBinaryHeap(pq) && y in Elements(pq)
      ensures pq.x <= y
    {
        if pq.Node? {
            assert y in Elements(pq) ==> (y == pq.x
                || y in Elements(pq.left) 
                || y in Elements(pq.right));
            if y == pq.x {
                assert pq.x <= y;
            } else if y in Elements(pq.left) {
                assert pq.x <= pq.left.x;
                BinaryHeapStoresMin(pq.left, y);
                assert pq.x <= y;
            } else if y in Elements(pq.right) {
                assert pq.x <= pq.right.x;
                BinaryHeapStoresMin(pq.right, y);
                assert pq.x <= y;
            }
        }
    }

    lemma EmptyCorrect()
      ensures Valid(Empty()) && Elements(Empty()) == multiset{}
    { // unfold Empty()
    }
    
    lemma IsEmptyCorrect(pq: PQueue)
      requires Valid(pq)
      ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
    {
        if Elements(pq) == multiset{} {
            assert pq.Leaf?;
        }
    }
    
    lemma InsertCorrect(pq: PQueue, y: int)
      requires Valid(pq)
      ensures var pq' := Insert(pq, y);
        Valid(pq') && Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
    {}

    lemma RemoveMinCorrect(pq: PQueue)
      requires Valid(pq)
      requires !IsEmpty(pq)
      ensures var (y, pq') := RemoveMin(pq);
              Elements(pq) == Elements(pq') + multiset{y} &&
              IsMin(y, Elements(pq)) &&
              Valid(pq')
    {
        DeleteMinCorrect(pq);
    }
    
    lemma DeleteMinCorrect(pq: PQueue)
      requires Valid(pq) && !IsEmpty(pq)
      ensures var pq' := DeleteMin(pq);
        Valid(pq') && Elements(pq') + multiset{pq.x} == Elements(pq)
    // TODO

    ghost predicate IsMin(y: int, s: multiset<int>) {
        y in s && forall x :: x in s ==> y <= x
    }
}

// Ex 10.0, 10.1
module PQueueClient {
    import PQ = PQueue

    method Client() {
        var pq := PQ.Empty();
        PQ.EmptyCorrect();
        assert PQ.Elements(pq) == multiset{};
        assert PQ.Valid(pq);
        PQ.InsertCorrect(pq, 1);
        var pq1 := PQ.Insert(pq, 1);
        assert 1 in PQ.Elements(pq1);

        PQ.InsertCorrect(pq1, 2);
        var pq2 := PQ.Insert(pq1, 2);
        assert 2 in PQ.Elements(pq2);

        PQ.IsEmptyCorrect(pq2);
        PQ.RemoveMinCorrect(pq2);
        var (m, pq3) := PQ.RemoveMin(pq2);        

        PQ.IsEmptyCorrect(pq3);
        PQ.RemoveMinCorrect(pq3);
        var (n, pq4) := PQ.RemoveMin(pq3);        

        PQ.IsEmptyCorrect(pq4);
        assert PQ.IsEmpty(pq4);

        assert m <= n;
    }
}