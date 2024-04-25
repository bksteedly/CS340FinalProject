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
    index: one Index
}

sig Value {}
sig Index {}

------------------------- State change predicates -----------------------------

pred init {
	no head
	no nextNode
	no tail
}

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
	some m: Node | {
		List.tail = m.nextNode
		List.tail.val = v
		nextNode' = nextNode - (m -> m.nextNode)
		List.tail' = m
		List.head' = List.head
	}
}

pred delete[v: one Value, i: one Index] {
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

pred insert[v: one Value, i: one Index] {
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
    	always (some v: Value | insertAtHead[v] or insertAtTail[v] or deleteAtHead[v] or deleteAtTail[v] or some i: Index | delete[v, i] or insert[v, i])
}

------------------ Predicates to check expected outcomes ----------------------

pred deleteThenInsertAtHead {
	all v: Value | (deleteAtHead[v] and after insertAtHead[v]) => {
		List.head.val = List.head''.val
		nextNode'' - (List.head'' -> List.head''.nextNode'') = nextNode - (List.head -> List.head.nextNode) 
	}
}
--run { deleteAndInsertAtHead } for 4

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

--run { deleteAndInsertAtTail } for 4


pred deleteThenInsertSamePlace {
	all v: Value, i: Index | (delete[v, i] and after insert[v, i]) => {
		List.head.val = List.head''.val
		nextNode'' - (List.head'' -> List.head''.nextNode'') = nextNode - (List.head -> List.head.nextNode) 
	}
}

run { deleteThenInsertSamePlace} for 4


assert alwaysDeleteThenInsertAtHead { always deleteThenInsertAtHead }
check alwaysDeleteThenInsertAtHead

assert alwaysDeleteThenInsertAtTail { always deleteThenInsertAtTail }
check alwaysDeleteThenInsertAtTail

assert alwaysDeleteThenInsertSamePlace { always deleteThenInsertSamePlace }
check alwaysDeleteThenInsertSamePlace
