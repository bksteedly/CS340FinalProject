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

fact {
	all n, m: Node | (n -> m in nextNode) => n.index < m.index
 	List.head.index = 0 
	all n: Node | List.tail != n => n.index < List.tail.index
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
		n.index' = List.head.index
		List.head.index' = 1
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
			m.index' = List.tail.index + 1
			List.tail.index' = List.tail.index
			List.tail' = m
			List.head' = List.head
		}
	}
}

run insertAtTail

pred deleteAtHead[v: one Value] {
	some List.head
	some List.tail
	some n: Node | {
		List.head = n
		n.val = v
		nextNode' = nextNode - (n -> n.nextNode)
		n.nextNode.index' = List.head.index
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
		m.index' = List.tail.index
		List.tail' = m
		List.head' = List.head
	}
}

pred insert[v: one Value, i: one Int] {
	some n: Node | { // this is the node we are inserting
		some m: Node | { // this is the node before the one we are inserting
			n not in List.head.^nextNode
			m.nextNode.index = i
			n.index' = i
			m.index' = m.index
			m.nextNode'.index' = i + 1
			nextNode' = nextNode + (m -> n) + (n -> m.nextNode) - (m -> m.nextNode)
			
		}
	}
}

run insert

pred delete[i: one Int] {
	some List.head
	some List.tail
	some n: Node | { // i is the index of the node we want to delete (n)
		some m: Node | { // m is the node before the node we want to delete
			n.index = i
			m.nextNode = n
			n.nextNode.index' = n.index
			m.index' = m.index
			nextNode' = nextNode + (m -> n.nextNode) - (m -> n) - (n -> n.nextNode)
		}
	}
}

run delete


------------------------------ Valid traces fact ------------------------------

fact validTraces {
	init
    	always (some v: Value, i: Int | insertAtHead[v] or insertAtTail[v] or deleteAtHead[v] or deleteAtTail[v] or delete[i] or insert[v, i])
}

------------------ Predicates to check expected outcomes ----------------------

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



pred deleteThenInsertSamePlace {
	init
	some v: Value, i: Int | {
		delete[i]
		after insert[v, i]
	}
}

pred deleteThenInsertAtHead {
	all v: Value | (deleteAtHead[v] and after insertAtHead[v]) => {
		List.head.val = List.head''.val
		nextNode'' - (List.head'' -> List.head''.nextNode'') = nextNode - (List.head -> List.head.nextNode) 
	}
}



pred deleteThenInsertAtTail {
	all v: Value | (deleteAtTail[v] and after insertAtTail[v]) => {
		some m: Node {
			List.tail = m.nextNode
			List.tail'' = m.nextNode
		
			List.tail''.val = List.tail.val
			nextNode'' - (m -> List.tail'') = nextNode - (m -> List.tail) 
		}
	}
}

assert alwaysDeleteThenInsertAtHead { always deleteThenInsertAtHead }
check alwaysDeleteThenInsertAtHead

assert alwaysDeleteThenInsertAtTail { always deleteThenInsertAtTail }
check alwaysDeleteThenInsertAtTail


run { validList } for 10
run { deleteThenInsertAtHead } for 10
run { deleteThenInsertAtTail } for 10




