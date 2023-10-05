
// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

// FIXME: fill in here (solution: 13 lines)
datatype Variables = Variables(server: nat, clients: seq<bool>) {
  ghost predicate WellFormed() {
    0 <= server <= |clients| // server == |clients| implies server holds lock
  }
}
// END EDIT


ghost predicate Init(v:Variables) {
  && v.WellFormed()
  // FIXME: fill in here (solution: 3 lines)
  && v.server == |v.clients|
  && forall i | 0 <= i < |v.clients| :: v.clients[i] == false
  // END EDIT
}
// FIXME: fill in here (solution: 23 lines)
ghost predicate Acquire(v:Variables, v':Variables, clientIndex: nat) {
  && v.WellFormed()
  && v'.WellFormed()
  && |v.clients| == |v'.clients| // clients don't change
  && v.server == |v.clients| // server used to hold lock
  && clientIndex < |v.clients|
  && v' == v.(server := clientIndex, clients := v.clients[clientIndex := true])
}

ghost predicate Release(v:Variables, v':Variables, clientIndex: nat) {
  && v.WellFormed()
  && v'.WellFormed()
  && |v.clients| == |v'.clients| // clients don't change
  && v.server == clientIndex // client used to hold lock
  && clientIndex < |v.clients|
  && v' == v.(server := |v.clients|, clients := v.clients[clientIndex := false])
}
// END EDIT
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
    // FIXME: fill in here (solution: 2 lines)
    | AcquireStep(clientIndex: nat)
    | ReleaseStep(clientIndex: nat)
    // END EDIT

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // FIXME: fill in here (solution: 2 lines)
   case AcquireStep(clientIndex) => Acquire(v, v', clientIndex)
   case ReleaseStep(clientIndex) => Release(v, v', clientIndex)
  // END EDIT
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(v:Variables) {
  // FIXME: fill in here (solution: 10 lines)
  forall i | 0 <= i < |v.clients|, j | i < j < |v.clients| :: !(v.clients[i] && v.clients[j])
  // END EDIT
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  // FIXME: fill in here (solution: 1 line)
  && clientIndex < |v.clients|
  && v.clients[clientIndex]
  // END EDIT
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (behavior:seq<Variables>)
  requires clientA == 2
  requires clientB == 0
  ensures 2 <= |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i]) // Behavior always satisfies the Safety predicate
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling ClientHoldsLock
  ensures ClientHoldsLock(behavior[1], clientA) // first clientA acquires lock
  ensures ClientHoldsLock(behavior[|behavior|-1], clientB) // eventually clientB acquires lock
{
  // FIXME: fill in here (solution: 9 lines)
  var v1 := Variables(server := 3, clients := [false, false, false]);

  var v2 := v1.(server := clientA, clients := v1.clients[clientA := true]);
  assert NextStep(v1, v2, AcquireStep(clientA));

  var v3 := v2.(server := 3, clients:= [false,false, false]);
  assert NextStep(v2, v3, ReleaseStep(clientA));

  var v4 := v3.(server := clientB, clients := v3.clients[clientB := true]);
  assert NextStep(v3, v4, AcquireStep(clientB));

  behavior := [v1, v2, v3, v4];
  // END EDIT
}
