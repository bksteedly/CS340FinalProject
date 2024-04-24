one sig List {
    // The top of the stack changes over time.
    var head: lone Node
}

sig Node {
    // nextNode is the next node after this one in the linked list. 
    // nextNode changes over time.
    var nextNode: lone Node,
    val: one Value
}
/* 
  The field nextNode is a relation with type Node -> Node. If a Node is not 
  currently in the stack, it should not be included in the nextNode relation 
  at all. A node should not exist multiple times in the linked list. Your model
  for the `push` and `pop` predicates should enforce these requirements.
*/

sig Value {}

------------------------- State change predicates -----------------------------

/* The model starts with an empty stack. */
pred init {
	no head
	no nextNode
}

--run init

/* The current step is a push of the value v. */
pred insertAtHead[v: one Value] {

  // This is a pattern for how we can say: on pushing a node, we need a node 
  // to store the value. Note that this does not yet enforce the requirements 
  // about whether n is already in the stack (that's your task!). 
	some n: Node | {
		--{ no m: Node | n in m.nextNode or m in n.nextNode }
		n not in List.head.^nextNode  
		n.val = v
		List.head != n
		nextNode' = nextNode + (n -> List.head)
		List.head' = n
  	}
}

pred insertAtTail[v: one Value] {
	some n: Node | {
		no n.nextNode
		some m: Node | {
			m not in List.head.^nextNode  
			m.val = v
			nextNode' = nextNode + (n -> m)
		}
	}
}

/* The current step is a pop that returns the value v.  */
pred deleteAtHead[v: one Value] {
	some List.head
	some n: Node | {
		List.head = n
		n.val = v
		nextNode' = nextNode - (n -> n.nextNode)
		List.head' = n.nextNode
	}
}

pred deleteAtTail[v: one Value] {
	some List.head
	some m: Node | {
		no m.nextNode.nextNode
		//one m: Node | {
//			m.nextNode = n 
//		}
		m.nextNode.val = v
		nextNode' = nextNode - (m -> m.nextNode)
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

pred deleteAndInsertAtHead {
	all v: Value | (deleteAtHead[v] and after insertAtHead[v]) => {
		List.head.val = List.head''.val
		nextNode'' - (List.head'' -> List.head''.nextNode'') = nextNode - (List.head -> List.head.nextNode) 
	}
}

run { deleteAndInsertAtHead } for 10


pred deleteAndInsertAtTail {
	all v: Value | (deleteAtTail[v] and after insertAtTail[v]) => {
		some m: Node {
			no m.nextNode.nextNode
		}
		List.head.val = List.head''.val
		nextNode'' - (List.head'' -> List.head''.nextNode'') = nextNode - (List.head -> List.head.nextNode) 
	}
}






