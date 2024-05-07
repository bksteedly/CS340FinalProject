from hypothesis import given, strategies as st

class Node:
    def __init__(self, data):
        self.data = data
        self.next = None

 
class BrokenLL:
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

    """
    Broken implementation: Does not handle the case where there is no head 
    and does not initialize the currentNode variable
    """
    def deleteAtIndex(self, index):
        # if self.head is None:
        #     return
 
        # currentIndex = 0
        # currentNode = self.head
        # if index == 0:
        #     self.deleteAtHead()
        #     return
        # else:
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
@given(st.lists(st.integers()), st.integers(min_value=0))
def test_deleteAtIndex(values, index):
    linkedList = BrokenLL()
    for value in values:
        linkedList.insertAtTail(value)
    
    index = min(index, len(values) - 1)  # Ensure index is within range
    linkedList.deleteAtIndex(index)
    
    firstHalf = values[:index]
    secondHalf = values[index+1:]
    assert linkedList.convertToList() == firstHalf + secondHalf

def main():
    test_deleteAtIndex()

if __name__ == "__main__":
    main()