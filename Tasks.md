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
- [x] Write down explanation of M&S Queue with locks (in latex)
- [ ] Write down explanation of lock-free M&S Queue (in latex)

- [x] State and prove correctness of M&S queue with locks (non-concurrent)
  - [x] Locks protect nothing (True) and all resources are always available (not duplicable, hence non-concurrent)
  - [x] Track exact contents of queue
  - [x] Implement proof in Iris

- [x] State and prove correctness of M&S queue with locks (concurrent case)
  - [x] Change initialise so that locks are created before head and tail.
  - [x] Define queue Invariant
  - [x] Change l_null to l_n+1
  - [x] Do proof sketch on paper
  - [x] Implement proof in Iris (Coq)
  - [x] Add a predicate that should hold of all elements in queue (see isBag)
  - [x] use {} and [] instead of i: 
  - [ ] Rename xs_rest to xs_queue
  - [ ] Prove consistency of is_queue

- [ ] Clean up proof of concurrent spec for M&S queue with locks in Coq
- [x] Clean up proof of Sequential spec for M&S queue with locks in Coq

- [ ] Write about the sequential spec for two-lock M&S queue in the report
  - [ ] Mention how it can be used to track exact contents of queue
  - [ ] Can be used to prove a precise spec for sequential client used in testing.
- [ ] Write about the concurrent spec for two-lock M&S queue in the report
  - [ ] Talk about adequacy as a reason for safety.
  - [ ] Update spec to include the Ψ predicate.

- [ ] State and prove correctness of lock-free M&S Queue
