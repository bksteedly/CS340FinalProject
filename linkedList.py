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
        else:
            currentNode = self.head
            while (currentNode.next.next):
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