- [x] Read Iris Technical Reference
- [x] Read Iris from the ground up
- [x] Read OFE file in theories
- [x] Finish Iris-Tutorial
- [x] Find out if bug in M&S queue dequeue when only 1 node (outside of the dummy node) (Conclusion: No bug)
- [x] Implement lock-free in C ignoring pointer struct (and with memory leak: i.e. no free)
- [x] Implement lock-free in Java
- [x] Implement Two-Lock MS-Queue in HeapLang
  - [x] Create an extra pointer reference to nodes, so that Head and Tail updates can be done as stores and so that compares can be done between pointers instead of pairs (See Contextual Refinement Paper) - needed to do assignments like: Q–>Tail = node

- [x] Study the Agreement RA
- [x] Read Contextual Refinement Paper
- [ ] Read chapter 13 of Iris Lecture Notes (Hocap style Specs)

- [x] Create Thesis Report file
- [x] Add bibliography (Iris-Lecture-Notes, Contextual Refinement Paper, Iris from Ground up, etc)

- [x] Read and understand M&S queue with locks
- [ ] Write down explanation of M&S Queue with locks (in latex)
- [ ] Write down explanation of lock-free M&S Queue (in latex)

- [ ] State and prove correctness of M&S queue with locks (non-concurrent)
  - [ ] Locks protect nothing (True) and all resources are always available (not duplicable, hence non-concurrent)
  - [ ] Track exact contents of queue
  - [ ] Implement proof in Iris
  - [ ] Prove correctness of simple client

- [ ] State and prove correctness of M&S queue with locks (concurrent case)
  - [x] Change initialise so that locks are created before head and tail.
  - [x] Define queue Invariant
  - [x] Change l_null to l_n+1
  - [x] Do proof sketch on paper
  - [ ] Implement proof in Iris (Coq)

- [ ] State and prove correctness of lock-free M&S Queue
