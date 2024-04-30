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
        
        currentIndex = 0
        currentNode = self.head
        if currentNode == index:
            self.insertAtHead(data)
        else:
            while (currentNode != None) and (currentIndex != index):
                if currentIndex == index - 1:
                    newNode.next = currentNode.next
                    currentNode.next = newNode
                    return 
                else:
                    currentNode = currentNode.next
                    currentIndex += 1
        
            print("Invalid index entered")
    
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
        else:
            currentIndex = 0
            currentNode = self.head
            if currentIndex == index:
                self.deleteAtHead()
            else:
                while (currentNode != None) and (currentIndex != index):
                    if currentIndex == index - 1:
                        currentNode.next = currentNode.next.next
                        return 
                    else:
                        currentNode = currentNode.next
                        currentIndex += 1
        
                print("Invalid index entered")
    
    def convertToList(self):
        result = []
        currentNode = self.head
        while currentNode:
            result.append(currentNode.data)
            currentNode = currentNode.next
        return result


@given(st.lists(st.integers()))
def test_insertAtHead(values):
    linkedList = LinkedList()
    
    for value in values:
        linkedList.insertAtHead(value)

    assert linkedList.convertToList() == list(reversed(values))

@given(st.lists(st.integers()))
def test_insertAtTail(values):
    linkedList = LinkedList()

    for value in values:
        linkedList.insertAtTail(value)

    assert linkedList.convertToList() == values

@given(st.lists(st.integers()), st.integers(min_value=1))
def test_deleteAtHead(values, n):
    linkedList = LinkedList()

    for value in values:
        linkedList.insertAtTail(value)

    numOfDeletes = min(n, len(values)) # don't delete more times than the length of the list
    for _ in range(numOfDeletes): 
        linkedList.deleteAtHead()
    assert linkedList.convertToList() == values[numOfDeletes:]

@given(st.lists(st.integers()), st.integers(min_value=1))
def test_deleteAtTail(values, n):
    linkedList = LinkedList()

    for value in values:
        linkedList.insertAtTail(value)

    numOfDeletes = min(n, len(values)) # don't delete more times than the length of the list
    for _ in range(numOfDeletes): 
        linkedList.deleteAtTail()

    assert linkedList.convertToList() == values[:len(values) - numOfDeletes]


def main():
    test_insertAtHead()
    test_insertAtTail()
    test_deleteAtHead()
    test_deleteAtTail()
    print("All tests passed")

if __name__ == "__main__":
    main()