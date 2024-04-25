one sig List {
    var head: lone Node,
    var tail: lone Node
} {
    no tail.nextNode
    no nextNode.head
}

sig Node {
    var nextNode: lone Node,
    val: one Value
}

sig Value {}

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

------------------------------ Valid traces fact ------------------------------

/* 
  How should traces start? What options should happen on every step?
  Note that unlike the trash model from class, you should *not* include a 
  "doNothing" predicate in this model. 
*/
fact validTraces {
	init
    	always (some v: Value | insertAtHead[v] or insertAtTail[v] or deleteAtHead[v] or deleteAtTail[v])
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

assert alwaysDeleteThenInsertAtHead { always deleteThenInsertAtHead }
check alwaysDeleteThenInsertAtHead

assert alwaysDeleteThenInsertAtTail { always deleteThenInsertAtTail }
check alwaysDeleteThenInsertAtTail







