//fact to constrain that the index must be smaller than tail
// implement find
//head is zero
//for all pairs of nodes next to each other the left should be one more than the right
// for constraints on delete and insert preconditon that the number that's passed in is less than the length of the list


one sig List {
    var head: lone Node,
    var tail: lone Node
} {
    no tail.nextNode
    no nextNode.head
}

sig Node {
    var nextNode: lone Node,
    val: one Value,
    var index: disj Int
}

sig Value {}

------------------------- State change predicates -----------------------------

pred init {
	no head
	no nextNode
	no tail
}

run init

pred insertAtHead[v: one Value] {
	some n: Node | {
		n not in List.head.^nextNode  
		n.val = v
		List.head != n
		nextNode' = nextNode + (n -> List.head)
		List.head' = n
		List.tail' = List.tail
  	}
}

run insertAtHead

pred insertAtTail[v: one Value] {
	some n: Node | {
		List.tail = n
		some m: Node | {
			m not in List.head.^nextNode  
			m.val = v
			nextNode' = nextNode + (n -> m)
			List.tail' = m
			List.head' = List.head
		}
	}
}

pred deleteAtHead[v: one Value] {
	some List.head
	some List.tail
	some n: Node | {
		List.head = n
		n.val = v
		nextNode' = nextNode - (n -> n.nextNode)
		List.head' = n.nextNode
		List.tail' = List.tail
	}
}

pred deleteAtTail[v: one Value] {
	some List.head
	some List.tail
	some m: Node | {
		List.tail = m.nextNode
		List.tail.val = v
		nextNode' = nextNode - (m -> m.nextNode)
		List.tail' = m
		List.head' = List.head
	}
}

pred delete[i: one Int] {
	some List.head
	some List.tail
	some n: Node | { // i is the index of the node we want to delete (n)
		some m: Node | { // m is the node before the node we want to delete
			n.index = i
			m.nextNode = n
			nextNode' = nextNode + (m -> n.nextNode) - (m -> n) - (n -> n.nextNode)
		}
	}
}

pred insert[v: one Value, i: one Int] {
	some n: Node | { // this is the node we are inserting
		some m: Node | { // this is the node before the one we are inserting
			m.nextNode.index = i
			n.index' = i
			m.index' = m.index
			m.nextNode'.index' = i + 1
			nextNode' = nextNode + (m -> n) + (n -> m.nextNode) - (m -> m.nextNode)
			
		}

	}
}
------------------------------ Valid traces fact ------------------------------

/* 
  How should traces start? What options should happen on every step?
  Note that unlike the trash model from class, you should *not* include a 
  "doNothing" predicate in this model. 
*/
fact validTraces {
	init
    	always (some v: Value, i: Int | insertAtHead[v] or insertAtTail[v] or deleteAtHead[v] or deleteAtTail[v] or delete[i] or insert[v, i])
}

------------------ Predicates to check expected outcomes ----------------------

/*
  Some things to check:
  - No element can be the nextNode of multiple elements or have multiple 
     nextNodes.
  - If an element is not in the stack it should not have a nextNode or be 
     another element's nextNode.
  - An element cannot be its own nextNode.

  Note: until the trash model from class, the outermost "always" is included in
  the relevant "check" statement below, so you don't need to include it here.
*/
pred validList {
	// No element can be the nextNode of multiple elements or have multiple nextNodes
	no disj n1, n2: Node | n1.nextNode = n2.nextNode && some n1.nextNode
	all n: Node | lone n.nextNode

    // If an element is not in the stack, it should not have a nextNode or be another element's nextNode
    	no n: Node - List.head.^nextNode - List.head | n in n.nextNode
	no n: Node - List.head.^nextNode - List.head, m: Node | m.nextNode = n

    // An element cannot be its own nextNode
    	no n: Node | n = n.nextNode
}


pred deleteThenInsertAtHead {
	init
	some v: Value | {
		deleteAtHead[v]
		after insertAtHead[v]
	}
}

pred deleteThenInsertAtTail {
	init
	some v: Value | {
		deleteAtTail[v]
		after insertAtTail[v]
	}
}


pred deleteThenInsertSamePlace {
	init
	some v: Value, i: Int | {
		delete[i]
		after insert[v, i]
	}
}

run { validList } for 10

--run insert for 4
--run delete for 4
--run { deleteThenInsertAtHead } for 4
--run { deleteAndInsertAtTail } for 4
--run { deleteThenInsertSamePlace} for 4


//assert alwaysDeleteThenInsertAtHead { always deleteThenInsertAtHead }
//check alwaysDeleteThenInsertAtHead
//
//assert alwaysDeleteThenInsertAtTail { always deleteThenInsertAtTail }
//check alwaysDeleteThenInsertAtTail
//
//assert alwaysDeleteThenInsertSamePlace { always deleteThenInsertSamePlace }
//check alwaysDeleteThenInsertSamePlace
