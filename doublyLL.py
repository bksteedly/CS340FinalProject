from hypothesis import given, strategies as st

class Node:
    def __init__(self, data):
        self.data = data
        self.next = None
        self.prev = None

 
class DoublyLinkedList:
    def __init__(self):
        self.head = None

    def insertAtHead(self, data):
        newNode = Node(data)
        if self.head is None: 
            self.head = newNode
            return
        else: 
            self.head.prev = newNode
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
        newNode.prev = previousTail

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
                newNode.prev = currentNode
                if currentNode.next:
                    currentNode.next.prev = newNode
                currentNode.next = newNode
            else:
                print("Invalid index entered: ", index)
    
    def deleteAtHead(self):
        if self.head is None:
            return
        elif self.head.next is None:
            self.head = None
            return
        else:
            self.head = self.head.next
            self.head.prev = None
    
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
                if currentNode.next.next:
                    currentNode.next.next.prev = currentNode
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
    
    def reverseList(self):
        result = []
        currentNode = self.head
        while currentNode != None and currentNode.next:
            currentNode = currentNode.next

        startFromTail = currentNode
        while startFromTail != None and startFromTail.prev:
            result.append(startFromTail.data)
            startFromTail = startFromTail.prev

        if startFromTail:
            result.append(startFromTail.data)

        return result
    
# PBT
@given(st.lists(st.integers()))
def test_insertAtHead(values):
    linkedList = DoublyLinkedList()
    
    for value in values:
        linkedList.insertAtHead(value)

    # if we insert at the head, then the linked list should be in the opposite order as the values list
    assert linkedList.convertToList() == list(reversed(values))

    # if we use the prev pointers, then the linked list should have the same data order as the values list
    assert linkedList.reverseList() == values

@given(st.lists(st.integers()))
def test_insertAtTail(values):
    linkedList = DoublyLinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    # if we insert at the tail, then the linked list should be in the same order as the values list
    assert linkedList.convertToList() == values

    # if we use the prev pointers, then the linked list should be in the oppposite order as the values list
    assert linkedList.reverseList() == list(reversed(values)) 

@given(st.lists(st.integers()), st.integers(), st.integers(min_value=0))
def test_insertAtIndex(values, data, index):
    linkedList = DoublyLinkedList()
    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)
    
    index = min(index, len(values))  # Ensure index is within range
    linkedList.insertAtIndex(data, index)

    firstHalf = linkedList.convertToList()[:index]
    secondHalf = linkedList.convertToList()[index+1:]

    # check that all other node values before and after the newly inserted node remain the same
    assert firstHalf + secondHalf == values 

    # check that the prev pointers are correct by ensuring reverseList produces the reversed 
    # version of convertToList
    assert linkedList.reverseList() == list(reversed(linkedList.convertToList())) 

@given(st.lists(st.integers()), st.integers(min_value=1))
def test_deleteAtHead(values, n):
    linkedList = DoublyLinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    numOfDeletes = min(n, len(values)) # don't delete more times than the length of the list
    for _ in range(numOfDeletes): 
        linkedList.deleteAtHead()
    
    # all other node values after the deleted nodes should remain the same
    assert linkedList.convertToList() == values[numOfDeletes:]

    # if we use prev pointers, then the list should be in the reverse order 
    assert linkedList.reverseList() == list(reversed(values[numOfDeletes:]))

@given(st.lists(st.integers()), st.integers(min_value=1))
def test_deleteAtTail(values, n):
    linkedList = DoublyLinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    numOfDeletes = min(n, len(values)) # don't delete more times than the length of the list
    for _ in range(numOfDeletes): 
        linkedList.deleteAtTail()

    # all other node values before the deleted nodes should remain the same
    assert linkedList.convertToList() == values[:len(values) - numOfDeletes]

    # if we use prev pointers, then the list should be in the reverse order 
    assert linkedList.reverseList() == list(reversed(values[:len(values) - numOfDeletes]))

@given(st.lists(st.integers()), st.integers(min_value=0))
def test_deleteAtIndex(values, index):
    linkedList = DoublyLinkedList()
    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)
    
    index = min(index, len(values) - 1)  # Ensure index is within range
    linkedList.deleteAtIndex(index)
    
    firstHalf = values[:index]
    secondHalf = values[index+1:]

    # all nodes before and after the deleted node should be preserved 
    assert linkedList.convertToList() == firstHalf + secondHalf

    # if we use prev pointers, then the list should be in the reverse order 
    assert linkedList.reverseList() == list(reversed(firstHalf + secondHalf))

@given(st.lists(st.integers(), min_size=1), st.integers(), st.integers(min_value=0))
def test_deleteThenInsert(values, data, index):
    linkedList = DoublyLinkedList()

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

    # if we use prev pointers, then the list should be in the reverse order 
    assert linkedList.reverseList() == list(reversed(values[:index] + [data] + values[index+1:]))

@given(st.lists(st.integers(), min_size=1), st.integers(), st.integers(min_value=0))
def test_insertThenDelete(values, data, index):
    linkedList = DoublyLinkedList()

    for value in values:
        # inserting at tail => order of values is same in LL as the values list
        linkedList.insertAtTail(value)

    index = min(index, len(values) - 1) # Ensure index is within range

    linkedList.insertAtIndex(data, index)
    linkedList.deleteAtIndex(index)

    # the linked list should remain unchanged 
    assert linkedList.convertToList() == values

    # if we use prev pointers, then the list should be in the reverse order as the values list
    assert linkedList.reverseList() == list(reversed(values))

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