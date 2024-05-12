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
- [x] Reread about fancy update and view-shift (sections in chapter 14 ILN)
- [x] Reread about invariant namespaces (chapter 14.5 ILN)
- [x] Read chapter 13 of Iris Lecture Notes (Hocap style Specs)
- [ ] Read paper: The Future is Ours: Prophecy Variables in Separation Logic

- [x] Create Thesis Report file
- [x] Add bibliography (Iris-Lecture-Notes, Contextual Refinement Paper, Iris from Ground up, etc)

- [x] Read and understand M&S queue with locks
- [x] Write down explanation of M&S Queue with locks (in latex)
- [x] Write down explanation of lock-free M&S Queue (in latex)

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
  - [x] Rename xs_rest to xs_queue
  - [x] Prove consistency of is_queue
  - [x] Rename qg to Q_γ

- [x] State and prove Hocap style Spec of M&S queue with locks
  - [x] Make Q a proposition in enqueue
  - [x] Define notation for the ownership of the contents of the queue. (e.g. queue_content_auth and queue_content_frac)
  - [x] Don't mention iname. Use namespaces
  - [x] Move auth and All into same position in queue invariant

- [x] Clean up proof of concurrent spec for M&S queue with locks in Coq
  - [x] Clear unused variables and propositions
  - [x] Remove _2 and _3 from subsequent invariant accesses
- [x] Clean up proof of Sequential spec for M&S queue with locks in Coq
- [x] Change let N := ... into Notation (...) for namespaces.
- [x] Consider removing some of the CHANGE comments in hocap.
- [x] Consider changing indentation from 4 to 2.

- [x] Write about the sequential spec for two-lock M&S queue in the report
  - [x] Mention how it can be used to track exact contents of queue
  - [x] Can be used to prove a precise spec for sequential client used in testing
- [x] Write about the concurrent spec for two-lock M&S queue in the report
  - [ ] Talk about adequacy as a reason for safety
  - [x] Update spec to include the Ψ predicate
- [x] Write about HOCAP spec for two-lock M&S queue in the report
  - [x] motivate it from sequential and concurrent
  - [x] "Prove it" - mention differences from Concurrent
  - [x] Explain that it is more general that then previous two, and can in fact derive them (without referring to the implementation)
  - [x] Show how to derive concurrent and sequential specs from it
- [x] Update notation for definitions to use triangleq instead of equality

- [x] State and prove correctness of lock-free M&S Queue
  - [x] Add prophesies to dequeue (linearisation point could be early if the queue is empty)
  - [x] prove enqueue spec
  - [x] prove dequeue spec
  - [x] Might be possible to remove isLL xs (future work)
  - [x] Show the two derived specifications (similar to two-lock versions)
  - [x] Try to remove consistency check and see if spec is still provable (concussion: spec is still provable)

- [x] Clean up proofs and make consistent
  - [x] Make variable names consistent (fx: x_n vs x_head_next)
  - [x] Fix all todos in code
  - [x] create a name for first node, and the enqueued node
  - [x] _null -> to_none
  - [x] out -> to_xm
  - [x] in -> node
  - [x] x_n -> xn_
  - [x] remove redundant '
  - [x] rewrite with ssreflect (in most places). I.e. rewrite /Reach /=.
  - [x] create queue_case lemma
  - [x] fix indentation
  - [x] Consider renaming 'pt' to 'ap' for abstract points-to in lockfreeMSQ_hocap and lockAndCCfreeMSQ_hocap.

- [x] Introduce the notion of linearisation points
- [x] Point out the linearisation points in the proof outlines

- [ ] Create a section/chapter explaining some of the basic rules (hoare-triples, weakest-precondition, inv-alloc, resource algebra), and also iris in general.

- [x] Mention coq and iris version that the code works with.
- [x] Give an overview of Coq files and how they refer to sections in report. Perhaps mention it at beginning/end of each section, or just have an overview in a section (on the coq formalisation)
- [x] Mention how to compile the files (via _CoqProject and make)

- [x] Fix notation overload in Coq. Maybe just use the Q_g.g_abst => xs notation everywhere
- [ ] Make Twolock Hocap a Hocap queue
- [ ] Make derivations of concurrent and sequential independent of implementation
  - [ ] Update overview of files in report

- [x] Create better notation of nIn, nOut and nVal
- [x] Write macros for many of the predicates (queue_invariant isLast, etc.)
- [x] Wrap proofs of initialise, enqueue, and dequeue in begin{proof}
- [x] Add lemmas in sections when proving initialise, enqueue, and dequeue, showing exactly what we are proving (see lock-free proof outline).
- [ ] Add isLL lemmas in appendix
- [ ] Refer to nIn-equal lemma in proofs
- [x] change null / null node / ... to None
- [x] Consider not using the term "sentinel"
- [x] change "x" to ``x'', and similarly for 'x'
- [ ] Decide on name/notation for Qgnames (including SeqQgnames and ConcQgnames). Maybe \mathcal(G)_{\text{seq}}?
- [x] Center figures on page (not on line)
- [x] Make sure all node values are 'w' and queue values are 'v'
- [ ] Rewrite some of the proofs for two-lock
- [ ] Consider adding the specifications for the derivation proofs
- [x] Refer to line numbers in proofs for two-lock
- [ ] Check for correctness of line number references
- [ ] Format the forall intros in lemmas (and definitions) better.
- [ ] Consider changing is_queue to isQueue (and similarly for is_queue_seq and is_queue_conc)

- [x] fix readme
  - [x] formatting
  - [x] content
  - [x] correct version numbers

- [x] Create references to:
  - [x] Iris Technical Reference (if reader wishes to see the relevant technical definitions)
  - [x] Iris from the ground up (As a somewhat gentle introduction to concepts used for the Coq code)
  - [x] Iris Lecture Notes (see todos in report)
  - [x] Herlihy & Wing : Linearizability. #5 in MSQ paper

- [ ] If time permits, use hocap spec to prove a spec of a client