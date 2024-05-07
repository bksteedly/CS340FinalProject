# Linked List Modeling and Property-Based Testing

This project extends our modeling skills developed in CS340: Modeling for Computer Systems by modeling a singly and doubly linked list in Alloy and using our Python property-based testing skills to test properties of a singly and doubly linked list implementation. 

## Project Overview

We modeled a stack for a previous assignment, so modeling a singly and doubly linked list and adding additional functionality like being able to insert at any point in the list seemed like a natural extension of this. We use temporal alloy to show the different states of the list as nodes are added or removed. In Alloy, we modeled inserting and deleting nodes at the head and tail in addition to modeling insert and delete at any index. We checked that the properties of the list are maintained while performing different operations, including:

- No node can be the nextNode of multiple nodes or have multiple nextNode relations.
- If an element is not in the linked list, it should not have a nextNode or be the nextNode of another node.
- No node can be its own nextNode.
- No node can be the prevNode of multiple nodes or have multiple prevNode relations.
- If an element is not in the linked list, it should not have a prevNode or be the prevNode of another node.
- No node can be its own prevNode.

To conduct property-based testing on our linked list implementation, we used the Python hypothesis library to generate random valid inputs and test the output of different linked list operations against properties we define for a linked list. 

For our property-based testing, we first implemented a singly linked list and doubly linked list implementation which have functions for inserting and deleting at the head and tail along with inserting and deleting at any index. We tested that properties of the linked list are maintained when each operation is performed. Additionally, we created a folder of broken singly linked list implementations where each file in the folder has one of the several operations be broken, in order to check that our PBT correctly identifies incorrect implementations.

## Required Tools

- **Alloy:** Alloy must be installed on your device in order to run the `.als` file. Installation instructions can be found [here](https://alloytools.org/download.html).
- **Python:** The `.py` files can be run using Python3 which can be installed using the following instructions: [Python Downloads](https://www.python.org/downloads/).
- **Hypothesis Library:** You will also need to install the Python hypothesis library using this link: [Installing Hypothesis](https://hypothesis.readthedocs.io/en/latest/quickstart.html#installing).

## How to Run the Code

### Alloy Model
To run either of the Alloy models, open the file in Alloy and click the execute button in the top toolbar. This will show a dropdown with all of the available run statements. Simply click on the run statement you would like to test. If the solver finds an instance, click on "Instance" to view the model. Note: You may have to comment out the validTraces fact to see instances of certain predicates, such as deleteAtHead. 

### Python Files
To run the Python files, run the corresponding commands in the terminal:

- `singlyLL.py`: `python3 singlyLL.py`
- `doublyLL.py`: `python3 doublyLL.py`
- `broken singlyLL implementations`: `python3 broken_singlyLL/{filename}` ex. `python3 broken_singlyLL/broken_deleteAtHead.py`

## Design Tradeoffs

- **Tail Variable:** Do we need a tail variable in addition to a head variable for our List sig in the Alloy model? We started by only including a head variable but soon realized that a tail variable would allow us to more easily remove nodes at the end of the linked list without having to traverse all nextNode pointers.
- **Index Type:** Should index be an integer or a sig? We first made the index field in the Node sig a sig, but then we realized that making it a variable integer would allow it to adapt as nodes are added and removed from the linked list.
- **Argument Passing:** When inserting and deleting at the head or the tail, what should we pass as arguments to the predicates? We were deciding whether to pass the head or the tail of the linked list as arguments to the insertAtHead, insertAtTail, deleteAtHead, and deleteAtTail predicates. We realized that it was simpler to just pass in the value to be inserted or deleted and just access the head or tail variable through the List sig.

## Limitations

Some of the limitations of our Alloy model were that only one node can be inserted or deleted at a time, so the model does not check for consistency when multiple nodes are inserted or deleted in the same step.

For our property-based testing, our design was limited by the need to set minimum values on certain randomly-generated inputs such as ensuring that the randomly-generated index has a minimum value of zero. Additionally, within our test functions, we checked that the randomly-generated index is not greater than the length of the linked list to ensure that it is a valid index.
