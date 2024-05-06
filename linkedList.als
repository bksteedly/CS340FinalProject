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
		some List.head => some List.tail
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
	  List.head = List.tail => {
		List.tail = m
		List.head = m
		m.val = v
		no nextNode'
		no List.head'
		no List.tail' 
	  }

	  List.head != List.tail => {
		some n: Node | {
			n.nextNode = m 
			m.val = v
			List.tail = m
        		nextNode' = nextNode - (n -> m)
        		List.tail' = n
			List.tail'.index' = n.index
			List.head' = List.head
		}
	  }
    }

	List.whichStep = deleteAtTail
}

run deleteAtTail

pred insert[v: one Value, i: one Int] {
	no List.head => {
		some n: Node | {
			n not in List.head.^nextNode
			List.head' = n
			n.index' = 0
			List.tail' = n
			no nextNode'
		}
	}
//	some List.tail => i <= List.tail.index or i = add[List.tail.index, 1]
	some List.head => {
		some n: Node | { // n is the node we're adding
			n not in List.head.^nextNode 
			some m: Node | { // m is the node before the one we're adding
				some m.nextNode => {
					m.nextNode.index = i
					m.nextNode.index' = add[i, 1]
					m.index' = m.index
					n.index' = i
					nextNode' = nextNode + (m -> n) + (n -> m.nextNode) - (m -> m.nextNode)
				}
				no m.nextNode => {
					n.index' = i
					List.tail' = n
					m.index' = m.index
					nextNode' = nextNode + (m -> n) 
				}
			}
		}
	}
	List.whichStep = insert
}

//m, m.nextNode

run insert


pred delete[i: one Int] {
	some List.head => i <= List.tail.index
	no List.head => i = 0

	List.head = List.tail => {
		some n: Node | {
			List.head = n
			List.tail = n
			no List.tail'
			no List.head'
			no nextNode'
		}
	}
	
	List.head != List.tail => {
		some n: Node | { // i is the index of the node we want to delete (n)
			n in List.head.^nextNode 
			n.index = i
			some m: Node | { // m is the node before the node we want to delete
				m.nextNode = n
				m.index' = m.index
				some n.nextNode => {
					n.nextNode.index' = n.index
					nextNode' = nextNode + (m -> n.nextNode) - (m -> n) - (n -> n.nextNode)
					List.tail' = List.tail 
					List.head' = List.head
				}
			
				no n.nextNode => {
					List.tail' = m
					nextNode' = nextNode - (m -> n)
					List.head' = List.head
				}
			}	
		}
	}
	List.whichStep = delete
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
	no disj n1, n2: Node | some n1.nextNode and (n1.nextNode = n2.nextNode )--&& some n1.nextNode
	all n: Node | lone n.nextNode

    // If an element is not in the list, it should not have a nextNode or be another element's nextNode
    	no n: Node - List.head.^nextNode - List.head | some n.nextNode
	no n: Node - List.head.^nextNode - List.head, m: Node | m.nextNode = n

    // An element cannot be its own nextNode
    	no n: Node | n = n.nextNode
	
}


pred insertThenDeleteAtHead {
	all v: Value | (insertAtHead[v] and after deleteAtHead[v]) => {
		List.head.val = List.head''.val
		nextNode = nextNode''
	}
}

pred insertThenDeleteAtTail {
	all v: Value | (insertAtTail[v] and after deleteAtTail[v]) => {
		List.tail.val = List.tail''.val
		nextNode = nextNode''
	}
}


assert alwaysValidList { always validList }
check alwaysValidList

assert alwaysInsertThenDeleteAtHead { always insertThenDeleteAtHead }
check alwaysInsertThenDeleteAtHead

assert alwaysInsertThenDeleteAtTail { always insertThenDeleteAtTail }
check alwaysInsertThenDeleteAtTail

run { insertThenDeleteAtHead } for 10
run { insertThenDeleteAtTail } for 10
