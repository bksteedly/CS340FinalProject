# CS340FinalProject

This project extends our modeling skills developed in CS340: Modeling for Computer Systems by modeling a singly linked list and using our Python property-based testing skills to test properties of a singly and doubly linked list implementation. We modeled a stack for a previous assignment, so modeling a linked list and adding additional functionality like being able to insert at any point in the list seemed like a natural extension of this. We use temporal alloy to show the different states of the list as nodes are added or removed. In Alloy, we modeled inserting and deleting nodes at the head and tail in addition to modeling insert and delete at any index. We checked that the properties of the list are maintained while performing different operations, including no node can be the nextNode of multiple nodes or have multiple next nodes, if an element is not in the linked list it should not have a nextNode or be the nextNode of another node, and no node can be its own nextNode. 

To conduct property-based testing on our linked list implementation, we used the python hypothesis library to generate random valid inputs and test the output of different linked list operations against properties we define for a linked list. For our PBT we first implemented a singly linked list and doubly linked list implementation which have functions for inserting and deleting at the head and tail along with inserting and deleting at any index. We tested that properties of the linked list are maintained when each operation is performed. 


Required tools: 
Alloy must be installed on your device in order to run the .als file. Installation instructions can be found here: https://alloytools.org/download.html. The .py files can be run using Python3 which can be installed using the following instructions: https://www.python.org/downloads/. You will also need to install the python hypothesis library using this link: https://hypothesis.readthedocs.io/en/latest/quickstart.html#installing

How to run the code:
To run the Alloy model, click the execute button in the top toolbar. This will show a dropdown with all of the available run statements. Simply click on a run statement you would like to test. If the solver finds an instance, click on "Instance" to view the model. 

To run the Python files, run the corresponding commands in the terminal: 
- singlyLL.py: "python3 singlyLL.py"
- doublyLL.py: "python3 doublyLL.py"
- brokenLL.py: "python3 broken_singlyLL/{filename}"
  ex. "python3 broken_singlyLL/broken_deleteAtHead.py"

Design tradeoffs:
- Do we need a tail variable in addition to a head variable for our List sig in the Alloy model?
  We started by only including a head variable but soon realized that a tail variable would allow us to more easily remove nodes at the end of the linked list without   having to traverse all nextNode pointers.
- Should index be an integer or a sig?
  We first made the index field in the Node sig a sig, but then we realized that making it a variable integer would allow it to adapt as nodes are added and removed from the linked list. 
- When inserting and deleting at the head or the tail, what should we pass as arguments to the predicates?
  We were deciding whether to pass the head or the tail of the linked list as arguments to the insertAtHead, insertAtTail, deleteAtHead, and deleteAtTail predicates. We realized that it was simpler to just pass in the value to be inserted or deleted and just access the head or tail variable through the List sig.

Limitations:
Some of the limitations of our Alloy model were that only one node can be inserted or deleted at a time, so the model does not check for consistency when multiple nodes are inserted or deleted in the same step. Additionally, we only modeled a singly linked list in Alloy so we could model a doubly linked list in future iterations of this project. For our property-based testing, our design was limited by the need to set minimum values on certain randomly-generated inputs such as ensuring that the randomly-generated index has a minimum value of zero. Additionally, within our test functions we checked that the randomly-generated index is not greater than the length of the linked list to ensure that it is a valid index. 
