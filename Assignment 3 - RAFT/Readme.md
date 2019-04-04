## In Search of an Understandable Consensus Algorithm

#### Presented by Ankush Phulia, 2014CS50279



### Introduction

*"All distributed consensus algorithms are either Paxos, Paxos with extra unnecessary cruft, or broken"*

​																	-- Mike Burrows

The key to building a consistent and reliable distributed system is being able to achieve consensus amongst the members. Since its publication, the Paxos algorithm has dominated the discussion of the means of attaining consensus in such a setting, most implementations are either Paxos or variants of it.

However, Paxos isn't a very simple algorithm. In fact, over the years it has gained notoriety for being extremely nuanced that may be difficult to grasp. Further, Paxos does not lend itself well to implementation - since the more practical "Multi-Paxos" was not really covered in much detail in the original papers, the implementations differ amongst themselves and even from the theoretical description. A consequence of this is that even though the protocol may have a proof, it may not to apply to the significantly different practical implementation.

Thus, in an attempt to address these issues, the authors, with the goals of correctness, efficiency, extensibility and most importantly, understandability, came up with the RAFT(Reliable, Replicated, Redundant, And Fault-Tolerant) protocol. Note that the authors acknowledge the subjectivity in "understandability", but regardless try to "simplify" the protocol by decomposing it into sub-problems which could be solved and explained independently.

***



### The Algorithm

#### The Assumptions

Raft consensus operates under the same set of assumptions as Multi-Paxos, namely

* Network communication between nodes is unreliable including network delays, partitions, and packet loss, duplication, and re-ordering
* Any write to persistent storage will be completed before crashing
* Nodes operate in an asynchronously and no upper bound exists for the delay of messages 
* Byzantine failures cannot occur
* Nodes are statically configured with a knowledge of all other nodes in the cluster, configuration is static
* Clients of the application must communicate with the cluster via the current leader, it is the responsibility of the client to determine which one of them is currently leader
* The state machines on each node start in the same state and respond deterministically to operations

#### The State Machines

![img](https://lh5.googleusercontent.com/KsxUNpzvPPPo7F5KUeL9DS2KzqI1M7I21UJ_gc6tkZiTPcIfF0DO9MrzwZIjuLUBb8zBwkAnYwUm48iLaUqGti2s41thlPlFUy7NH3mWCMcHdGc9Yq-fbTpDeanF05nDnyPOa69wvv0)

Each node runs a state machine locally, which undergoes deterministic transitions based on various operations. It is a deterministic state machine in the sense that given the same starting state and same chain of commands/transitions, the final state will be the same. In case of a RAFT cluster, the consensus needs to be reached on which operation/transition to take for all the nodes.

#### Leader Election

![ img](https://lh4.googleusercontent.com/is0DVEsF9Fa09jEfCAQqMuDZ2QuEu3peqCXlGjNc3xy0y06n8c9x0o7rNPMrGXTFsgmZI53RSwTqncxGtGBF25IC7Fz2TrAqgrGL9klACr7jp8S0O_IfH2qIc3uSxgCJWWPwvheAInI)

Each node participating in the election can be either of

* Follower - only respond to RPCs, but do not initiate any communication.

* Candidate - starts a new election, increments the term, requests votes from other followers. It will become a leader if it gains a majority of votes, or revert to a follower if someone else becomes leader

* Leader - sends heartbeats to all followers, thereby preventing timeouts in idle periods and new elections. An election comes to an end once a candidate secures the majority and become the leader

All of these roles have a randomized time-out, on the elapse of which all roles assume that the leader has crashed and convert to be candidates, triggering a new election and incrementing the current term

#### Strong Leadership

The key differentiating feature between RAFT and Paxos is the presence of "strong" leadership in the former. Contrary to other protocols, who may defer leader election to an oracle, RAFT integrates leader election as an essential part of the consensus protocol. Once a leader is elected, all decision-making is driven by it - all log entries flow from leader to followers. The responsibilities of the leader include

* All message passing can only be initialized by the leader(or a candidate)
* The leader takes care of all communication with the clients
* The system is only available when a leader has been elected and is alive

#### Log Replication

Once a server is established as leader, it can serve the clients requests - commands that are to be committed to the replicated state machine. 

1. Each command is assigned a term and index, to uniquely identify it within a log and appends it there
2. Leader then sends the command to each follower - telling it to append it to its log. In addition it also sends the command that is just before the new one in its own log
   * If the follower has the older command in its log, it appends the new command to its log and replies to leader with success
   * If the follower is missing the older command, it replies with failure and then the leader sends a new message, containing the second and third oldest commands, and so on, till it gets a success
   *  This creates an inductive property - If a follower accepts a new entry from the leader, it checks the consistency the leader’s previous entry with its own, which must have been accepted because of the consistency of the previous entry and so on
3. Once the leader has replicated its logs on the majority of the cluster (received majority successes), it commits the command, whereby each follower with the command in its log executes it and changes state. At this point the command is permanent and cannot be overwritten from the logs
4. When the leader has committed the command and received a majority of successes here as well, it relays the result back to the client

Raft assumes that the leader’s log is always correct. The cleanup of inconsistent replicated state happens during normal operation and is designed in such a way that normal operation converges all the logs![img](https://lh6.googleusercontent.com/MBs0rPNRDXEMpBdTL8rpHqFMDNWUpdZZnmwkl68dIZVpmppLp84XZoTNJ_GdKxh5d6KUZJn3xbn7oMDItO78DvGt-7y8Rr5LhB1_Ha_XH9JCsPCpGResrDQD2e_m_e123fd6HeETuiU)

***



### Properties

#### Safety

*"Nothing bad ever happens"*, ensure that the protocol works correctly on all corner cases

* Elections - since there cannot be multiple majorities given only one vote per node, there can never be more than one leader
* Commitment - logs entries are only committed when present on the majority of nodes. Further, they must be of the current leader's term, or must occur before an entry that is from the current term
* Log safety - once an log entry has been committed, it cannot be overwritten. Further it could have only been committed if it was on a majority of nodes, so it is correct
* Leader selection - nodes only vote for a candidate whose logs are more complete than theirs. This ensures election of the best possible leader
* Log consistency - it is a leader's job to ensure this. It will continue exchanging messages with a node till a majority of them are consistent with it
* Old/outdated leaders - followers only listen to leaders whose term is greater than or equal to theirs. This ensures that old leaders (somehow due to healed network partition) cannot commit their logs and will step down when they see a leader with higher term
* Client interaction - Only once a command has been logged, committed, and executed on the state machine of the leader, will it then respond. Every command is paired with a unique command id, respond only once to it.

#### Liveness

*"Something good eventually happens"*, ensure that the protocol makes progress

* Elections - the random timeouts the nodes have, as candidates ensure that the election as a whole is timed. If the election ends with no leader chosen, new elections are called with *different* random timeouts for each node. Thus eventually, a leader will be chosen (unlike the original vanilla Paxos, where proposers could duel ad infinitum)
* Client interaction - Since leader election is guaranteed to happen eventually, the client's operations will also be eventually be carried out, given that a majority of nodes in the cluster is always functioning

#### Consistency, Availability and Partition Tolerance

The CAP theorem states that a distributed system can guarantee at most two of the three properties - consistency, availability and partition tolerance. Since RAFT ensures that the state machine is consistent across at least a majority of the cluster members before it returns an output to the client, it guarantees strong consistency (in fact, it can guarantee linearizability semantics). 

Further, the various safety guarantees ensure that the system is partition tolerant as well, as it anyways had assumed unreliable(not malicious) channels with unbounded message delays.

What of availability? Clearly during leader elections(no leader) or when the majority of cluster nodes is down(can't commit anything new), the system cannot carry out the client's operations and thus is not available.

***



### Limitations and Alternatives

#### Constraints

From a purely performance standpoint, RAFT (and Paxos) aren't too impressive, given the amount of message that fly over the network for leader elections and for each new operation/commit. This large number of messages cause RAFT to have scalability issues.

If one was to re-visit the operating assumptions of RAFT, it can be clearly seen that there are two crucial assumptions which limit the scope of RAFT applications, namely the intolerance to Byzantine failures and the requirement of a static cluster configuration as well as the need to know the entire network topology for each node. Byzantine failures can be handled (PBFT), but the scalability issue become even more pronounced then.

These are limiting in the sense that RAFT clusters cannot deal with nodes going rogue/turning malicious, i.e. are not secured from within, and that there is no provision of anonymity since all nodes need to know and trust each other.

#### Beyond RAFT

##### Blockchains

Blockchains are similar to RAFT as they tackle the problem of asynchronous, distributed consensus as well. Not just that, they share many other traits as well, like the immutability of data (RAFT logs that are committed can only be appended to, similar to blocks) and the decisions being driven by the leader (globally elected vs. locally elected).

Blockchain technology looks promising as it is tolerant to byzantine faults, provides anonymity to the nodes and can handle dynamic network changes like nodes leaving/joining. It manages all of this while being more scalable than RAFT(although it isn't all that scalable, unless more recent work is considered).

##### Atomic Broadcasts

When the network is completely asynchronous and unordered, the full complexity of RAFT becomes a necessity. However, if one can provide a totally-ordered, atomic broadcast at the network level, then maintaining the consistency of replicas becomes almost trivial. But providing such a strong property essentially is just moving the co-ordination overhead from one layer to the one below it.

Now if one could find a property that is weaker than totally-ordered atomic broadcasts, but stronger than asynchronous messages, which can also be implemented efficiently for certain networks (in this case, data centers), one could end up with a more scalable solution. One such work deals with ordered, unreliable multi-casts - replace the consensus with network ordering.

***



### References

1. **Bui, A., and Fouchal, H.**, Eds. Procedings of the 6th International
   Conference on Principles of Distributed Systems. OPODIS 2002, Reims,
   France, December 11-13, 2002 (2002), vol. 3 of Studia Informatica Univer-
   salis, Suger, Saint-Denis, rue Catulienne, France
2. **Chandra, T. D., Griesemer, R., and Redstone**, **J.** Paxos made live:
   An engineering perspective. In Proceedings of the Twenty-sixth Annual ACM
   Symposium on Principles of Distributed Computing (New York, NY, USA,
   2007), PODC ’07, ACM, pp. 398–407
3. **Lamport, L.** The part-time parliament. ACM Trans. Comput. Syst. 16, 2
   (1998), 133–169
4. **Li, J., Michael, E., Sharma, N. K., Szekeres, A., and Ports, D.**
   **R. K.** Just say NO to paxos overhead: Replacing consensus with network
   ordering. In 12th USENIX Symposium on Operating Systems Design and
   Implementation (OSDI 16) (Savannah, GA, 2016), USENIX Association,
   pp. 467–483
5. **Ongaro, D., and Ousterhout, J.** In search of an understandable consen-
   sus algorithm. In Proceedings of the 2014 USENIX Conference on USENIX
   Annual Technical Conference (Berkeley, CA, USA, 2014), USENIX ATC’14,
   USENIX Association, pp. 305–320.
6. **Howard, H.**, ARC: Analysis of Raft Consensus

***