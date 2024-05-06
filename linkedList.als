abstract sig Step {}
one sig insertAtHead, insertAtTail, deleteAtHead, deleteAtTail, insert, delete extends Step {}

one sig List {
    var head: lone Node,
    var tail: lone Node,
    var whichStep: Step 
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
	always {
		all n, m: Node | (n -> m in nextNode) => m.index = add[n.index, 1]
 		some List.head => List.head.index = 0
		List.head != List.tail => List.tail in List.head.^nextNode
	}
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
		nextNode' = nextNode + (n -> List.head)
		n.index' = 0
		List.head' = n
		List.head != List.tail => {
			List.tail' = List.tail
			List.tail'.index' = List.tail.index
		}

		List.head = List.tail => {
			List.tail' = n
		}
  	}
	List.whichStep = insertAtHead
}

run insertAtHead

pred insertAtTail[v: one Value] {
	some List.tail => {
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

	no List.tail => {
		some n: Node | {
			n not in List.head.^nextNode
			n.val = v
			nextNode' = nextNode
			n.index' = 0
			List.head' = n
			List.tail' = n
		}
	}

	List.whichStep = insertAtTail
}

run insertAtTail

pred deleteAtHead[v: one Value] {
    some List.head
    some n: Node | {

	  List.head = n
        n.val = v

        List.head = List.tail=> {
		List.tail = n
            no List.tail'
		no List.head'
            no nextNode'
        }

        List.head != List.tail => {
		List.head' = n.nextNode
            List.tail' = List.tail
		List.tail'.index' = List.tail.index
            nextNode' = nextNode - (n -> n.nextNode)
        }
    }
	List.whichStep = deleteAtHead
}

run deleteAtHead


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

fact validTraces {
    init
    always (some v: Value, i: Int | insertAtHead[v] or insertAtTail[v] or deleteAtHead[v] or deleteAtTail[v] or delete[i] or insert[v, i])
}

------------------ Predicates to check expected outcomes ----------------------

pred validList {
	// No element can be the nextNode of multiple elements or have multiple nextNodes
	no disj n1, n2: Node | some n1.nextNode and (n1.nextNode = n2.nextNode )--&& some n1.nextNode
//	all n: Node | lone n.nextNode
//
//    // If an element is not in the list, it should not have a nextNode or be another element's nextNode
//    	no n: Node - List.head.^nextNode - List.head | some n.nextNode
//	no n: Node - List.head.^nextNode - List.head, m: Node | m.nextNode = n
//
//    // An element cannot be its own nextNode
//    	no n: Node | n = n.nextNode
	
}


pred validList {
	// No element can be the nextNode of multiple elements or have multiple nextNodes
	no disj n1, n2: Node | some n1.nextNode and (n1.nextNode = n2.nextNode )--&& some n1.nextNode
	all n: Node | lone n.nextNode

      // If an element is not in the list, it should not have a nextNode or be another element's nextNode
    	no n: Node - List.head.^nextNode - List.head | n in n.nextNode
	no n: Node - List.head.^nextNode - List.head | n in List.head.^nextNode

      // An element cannot be its own nextNode
    	no n: Node | n = n.nextNode
	
}

pred insertThenDeleteAtHead {
	all v: Value | (insertAtHead[v] and after deleteAtHead[v]) => {
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
