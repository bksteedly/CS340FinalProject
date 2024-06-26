from hypothesis import given, strategies as st

class Node:
    def __init__(self, data):
        self.data = data
        self.next = None

 
class LinkedList:
    def __init__(self):
        self.head = None

    def insertAtHead(self, data):
        newNode = Node(data)
        if self.head is None: 
            self.head = newNode
            return
        else: 
            newNode.next = self.head 
            self.head = newNode
    
    def insertAtTail(self, data):
        newNode = Node(data)
        if self.head is None: 
            self.head = newNode
            return
        else:
            previousTail = self.head
            while(previousTail.next):
                previousTail = previousTail.next
 
        previousTail.next = newNode

    def insertAtIndex(self, data, index):
        newNode = Node(data)
        currentNode = self.head
        currentIndex = 0
        if index == 0:
            self.insertAtHead(data)
            return
        else:
            while(currentNode != None and currentIndex+1 != index):
                currentNode = currentNode.next
                currentIndex += 1
 
            if currentNode != None: 
                newNode.next = currentNode.next
                currentNode.next = newNode
            else:
                print("Invalid index entered: ", index)
    
    def deleteAtHead(self):
        if self.head is None:
            return
        else:
            self.head = self.head.next
    
    def deleteAtTail(self):
        if self.head is None:
            return
        elif self.head.next is None:
            self.head = None
            return
        else:
            currentNode = self.head
            while currentNode.next.next:
                currentNode = currentNode.next
            
            currentNode.next = None

    def deleteAtIndex(self, index):
        if self.head is None:
            return
 
        currentIndex = 0
        currentNode = self.head
        if index == 0:
            self.deleteAtHead()
            return
        else:
            while(currentNode != None and currentIndex+1 != index):
                currentNode = currentNode.next
                currentIndex += 1
 
            if currentNode != None:
                currentNode.next = currentNode.next.next
            else:
                print("Invalid index entered:", index)
    
    def convertToList(self):
        result = []
        currentNode = self.head
        while currentNode:
            result.append(currentNode.data)
            currentNode = currentNode.next
        return result

# PBT 
@given(st.lists(st.integers()))
def test_insertAtHead(values):
    linkedList = LinkedList()
    
    for value in values:
        linkedList.insertAtHead(value) 
        
    # if we insert at the head, then the linked list will be in the opposite order as the values list
    assert linkedList.convertToList() == list(reversed(values)) 

@given(st.lists(st.integers()))
def test_insertAtTail(values):
    linkedList = LinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    # if we insert at the tail, then the linked list will be in the same order as the values list
    assert linkedList.convertToList() == values

@given(st.lists(st.integers()), st.integers(), st.integers(min_value=0))
def test_insertAtIndex(values, data, index):
    linkedList = LinkedList()
    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)
    
    index = min(index, len(values))  # Ensure index is within range
    linkedList.insertAtIndex(data, index)

    firstHalf = linkedList.convertToList()[:index]
    secondHalf = linkedList.convertToList()[index+1:]

    # check that all other node values before and after the newly inserted node remain the same
    assert firstHalf + secondHalf == values

@given(st.lists(st.integers()), st.integers(min_value=1))
def test_deleteAtHead(values, n):
    linkedList = LinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    numOfDeletes = min(n, len(values)) # don't delete more times than the length of the list
    for _ in range(numOfDeletes): 
        linkedList.deleteAtHead()
    
    # all other node values after the deleted nodes should remain the same
    assert linkedList.convertToList() == values[numOfDeletes:]

@given(st.lists(st.integers()), st.integers(min_value=1))
def test_deleteAtTail(values, n):
    linkedList = LinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    numOfDeletes = min(n, len(values)) # don't delete more times than the length of the list
    for _ in range(numOfDeletes): 
        linkedList.deleteAtTail()

    # all other node values before the deleted nodes should remain the same
    assert linkedList.convertToList() == values[:len(values) - numOfDeletes]

@given(st.lists(st.integers()), st.integers(min_value=0))
def test_deleteAtIndex(values, index):
    linkedList = LinkedList()
    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)
    
    index = min(index, len(values) - 1)  # Ensure index is within range
    linkedList.deleteAtIndex(index)
    
    firstHalf = values[:index]
    secondHalf = values[index+1:]

    # all nodes before and after the deleted node should be preserved 
    assert linkedList.convertToList() == firstHalf + secondHalf

@given(st.lists(st.integers(), min_size=1), st.integers(), st.integers(min_value=0))
def test_deleteThenInsert(values, data, index):
    linkedList = LinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    index = min(index, len(values) - 1) # Ensure index is within range

    linkedList.deleteAtIndex(index)
    linkedList.insertAtIndex(data, index)

    assert len(linkedList.convertToList()) == len(values)  

    # nodes before and after the newly inserted node should have the same values and be
    # separated by the new node's data value
    assert linkedList.convertToList() == values[:index] + [data] + values[index+1:] 

@given(st.lists(st.integers(), min_size=1), st.integers(), st.integers(min_value=0))
def test_insertThenDelete(values, data, index):
    linkedList = LinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    index = min(index, len(values) - 1) # Ensure index is within range

    linkedList.insertAtIndex(data, index)
    linkedList.deleteAtIndex(index)

    # the linked list should remain unchanged 
    assert linkedList.convertToList() == values

def main():
    test_insertAtHead()
    test_insertAtTail()
    test_insertAtIndex()
    test_deleteAtHead()
    test_deleteAtTail()
    test_deleteAtIndex()
    test_deleteThenInsert()
    test_insertThenDelete()
    print("ALL TESTS PASSED!")

if __name__ == "__main__":
    main()