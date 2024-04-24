/* 

Goal: model a last-in, first-out (LIFO) stack backed by a linked-list. 

*/
one sig Stack {
    // The top of the stack changes over time.
    var top: lone Node
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
	no top
	no nextNode
}

--run init

/* The current step is a push of the value v. */
pred push[v: one Value] {

  // This is a pattern for how we can say: on pushing a node, we need a node 
  // to store the value. Note that this does not yet enforce the requirements 
  // about whether n is already in the stack (that's your task!). 
	some n: Node | {
		--{ no m: Node | n in m.nextNode or m in n.nextNode }
		n not in Stack.top.^nextNode  
		n.val = v
		Stack.top != n
		nextNode' = nextNode + (n -> Stack.top)
		Stack.top' = n
  	}
}

--run push

/*  
  Run this to see two pushes in a row. Note that the trace may not make sense
  after the single push if you have not yet implemented validTraces.
*/
pred twoPushes {
  init
  some v1, v2: Value | push[v1] and after push[v2]
}

--run twoPushes

/* The current step is a pop that returns the value v.  */
pred pop[v: one Value] {
	some Stack.top
	some n: Node | {
		Stack.top = n
		n.val = v
		nextNode' = nextNode - (n -> n.nextNode)
		Stack.top' = n.nextNode
	}
}

--run pop

/*  
  Run this to see two pushes then a pop in a row. Note that the trace may not make
  sense after the events if you have not yet implemented validTraces.
*/
pred twoPushesThenPop {
  init
  some disj v1, v2: Value | {
    push[v1]
    after push[v2]
    after after pop[v2]
	--after after after pop[v1]
  }
}

--run twoPushesThenPop for 2

------------------------------ Valid traces fact ------------------------------

/* 
  How should traces start? What options should happen on every step?
  Note that unlike the trash model from class, you should *not* include a 
  "doNothing" predicate in this model. 
*/
fact validTraces {
	init
    	always (some v: Value | push[v] or pop[v])
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
pred validStack {
	// No element can be the nextNode of multiple elements or have multiple nextNodes
	no disj n1, n2: Node | n1.nextNode = n2.nextNode && some n1.nextNode
	all n: Node | lone n.nextNode

    // If an element is not in the stack, it should not have a nextNode or be another element's nextNode
    	no n: Node - Stack.top.^nextNode - Stack.top | n in n.nextNode
	no n: Node - Stack.top.^nextNode - Stack.top, m: Node | m.nextNode = n

    // An element cannot be its own nextNode
    	no n: Node | n = n.nextNode
}

/* 
  What should happen when a pop is followed by a push of the same value? 

  Note: you can get almost all the credit for this subpart by just talking about
  the top value in the Stack. 

  For the final 5 pts of credit, you should also constrain the nextNode relation 
  in the Stack. This is more difficult, since popping then pushing the same
  Value does not actually require the same Node be used (similar to how an 
  in-memory representation of a linked-list would actually work).

  Note: unlike the trash model from class, the outermost "always" is included in
  the relevant "check" statement below, so you don't need to include it here.
*/
pred popThenPush {
	all v: Value | (pop[v] and after push[v]) => {
		Stack.top.val = Stack.top''.val
		nextNode'' - (Stack.top'' -> Stack.top''.nextNode'') = nextNode - (Stack.top -> Stack.top.nextNode) 
	}
}

/* 
  Check that everything that was popped must have been pushed previously. 
  
  Note: unlike the trash model from class, the outermost "always" is included in
  the relevant "check" statement below, so you don't need to include it here.
*/
pred beforePop {
	all v: Value | pop[v] => once push[v]
}

/* 
  Whenever the stack is empty, the only event that can happen is a push.
  
  Note: unlike the trash model from class, the outermost "always" is included in
  the relevant "check" statement below, so you don't need to include it here.
*/
pred pushFollowsEmpty {
	no Stack.top => some v: Value | push[v] 
}

--run {}

/* 
  You should see valid instances when you run these, that match the expected cases.
*/
--  run { validStack } for 10
--  run { popThenPush } for 10
--  run { beforePop } for 10
--  run { pushFollowsEmpty } for 10

/* 
  You should see no counterexamples when you run these once you have added 
  valid bodies to each predicate.
*/
assert alwaysValidStack {  always validStack}
check alwaysValidStack

assert alwaysPopThenPush { always popThenPush }
check alwaysPopThenPush

assert alwaysBeforePop { always beforePop }
check alwaysBeforePop 

assert alwaysPushFollowsEmpty { always pushFollowsEmpty }
check alwaysPushFollowsEmpty 
