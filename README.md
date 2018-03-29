# Final-Year-Project

## A Verification of Hash Tables using Dafny - From Linear Probing to Hopscotch Hashing

### A final year project completed for the BSc Computer Science and Software Engineering in Maynooth University.

___

The installation instructions for the required tools are available [here](/installation.md).

The contents of this repository and its relationship to the submitted report is available [here](/contents.md).

___

### Abstract from the submitted report:
> Hash tables are a very popular data structure due to their O(1) time complexity for searching, insertion, and deletion. Verification of hash tables is, therefore, very important, as any errors would have far-reaching consequences. This project provides proofs of correctness for three hash table algorithms – linear probing, separate chaining, and hopscotch hashing. Where linear probing and separate chaining are tried and tested approaches, hopscotch hashing is relatively new and cutting edge due to its concurrent lock-free capabilities. The proofs presented use Dafny, a sequential verification language. Using an iterative approach, the proof of each algorithm is established by building up from a simpler example. Additionally, the portability of these proofs into the concurrent verification language VerCors is explored. It is determined that while the Dafny verification proved successful, the translation into VerCors is not a simple one, and that VerCors lacks the documentation for a new user to get to grips with the tool easily.