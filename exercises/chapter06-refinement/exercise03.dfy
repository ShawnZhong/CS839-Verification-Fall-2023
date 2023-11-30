// Refinement proof for 2PC
// Show that Two Phase Commit refines the Atomic Commit sate machine spec.

// This proof shouldn't be terribly brutal, since you have a roadmap for the
// relevant invariants from chapter05. You can discard the AC properties (since
// those are proven about the spec in exercise03, and therefore about any state
// machine that refines the spec).

include "exercise01.dfy"

// We have provided you with a copy of our solution to chapter05 exercises
// here. We're building on its state machine, so of course we need its definition.
// The Safety property that chapter 05 considered a "spec" is no longer a spec since
// we're going to use an abstract spec that the protocol refines; however,
// it's still really useful as an invariant, so we'll incorporate that
// property and its proof here as well.
include "ch05exercise03.dfy"

// This Dafny "abstract module" establishes the proof obligations for the
// refinement: later in the file you will be obligated to fill in the function
// and lemma bodies in a module that `refines` this one.
// (This structure is a nice way to separate the statement of the theorem from
// its proof.)
abstract module RefinementTheorem {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened TwoPCInvariantProof
  import AtomicCommit

  ghost function VariablesAbstraction(v: DistributedSystem.Variables) : AtomicCommit.Variables
    requires v.WF()

  ghost predicate Inv(v: DistributedSystem.Variables)

  lemma RefinementInit(v: DistributedSystem.Variables)
    requires DistributedSystem.Init(v)
    ensures Inv(v)
    ensures AtomicCommit.Init(VariablesAbstraction(v))

  lemma RefinementNext(v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    requires DistributedSystem.Next(v, v', event)
    requires Inv(v)
    ensures Inv(v')
    ensures AtomicCommit.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event) ||
            (VariablesAbstraction(v) == VariablesAbstraction(v') && event == NoOpEvent)

}

module RefinementProof refines RefinementTheorem {
  // No imports needed because we inherited them from the abstract module RefinementTheorem
  import opened Obligations
  import opened CoordinatorHost

  // Here are some handy accessor functions for dereferencing the coordinator
  // and the participants out of the sequence in Hosts.
  ghost function CoordinatorVars(v: DistributedSystem.Variables) : CoordinatorHost.Variables
    requires v.WF()
  {
    Last(v.hosts).coordinator
  }

  // Here's a handy function to save you some typing.
  ghost function ParticipantCount(v: DistributedSystem.Variables) : nat
    requires v.WF()
  {
    CoordinatorVars(v).c.participantCount
  }

  // The main challenge of setting up a refinement: abstracting from the
  // low-level (protocol) state to the high-level (spec) state.
  ghost function Preferences(v: DistributedSystem.Variables) : seq<Vote>
    requires v.WF()
  {
    // FIXME: fill in here (solution: 1 line)
    seq(ParticipantCount(v), i requires 0 <= i < ParticipantCount(v) => ParticipantVars(v, i).c.preference)
      // END EDIT
  }

  ghost function VariablesAbstraction(v: DistributedSystem.Variables) : AtomicCommit.Variables
  {
    // FIXME: fill in here (solution: 3 lines)
    var d := seq(ParticipantCount(v), i requires 0 <= i < ParticipantCount(v) => ParticipantVars(v, i).decision);
    AtomicCommit.Variables(Preferences(v), d)
    // END EDIT
  }

  ghost predicate Inv(v: DistributedSystem.Variables)
  {
    // Just point at the invariant from the chapter05 proof (in exercise03).
    // Be certain to fully-qualify the invariant name (mention its module
    // explicitly) to avoid inadvertently referring to the shadowing definition
    // RefinementTheorem.Inv.
    // FIXME: fill in here (solution: 1 line)
    TwoPCInvariantProof.Inv(v)
    // END EDIT
  }

  lemma RefinementInit(v: DistributedSystem.Variables)
    // Obligations inherited from RefinementTheorem.RefinementInit
    // requires DistributedSystem.Init(v)
    // ensures Inv(v)
    // ensures AtomicCommit.Init(VariablesAbstraction(v))
  {
  }

  lemma RefinementNext(v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    // Obligations inherited from RefinementTheorem.RefinementNext
    // requires DistributedSystem.Next(v, v', event)
    // requires Inv(v)
    // ensures Inv(v')
    // ensures AtomicCommit.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    // Advice: appeal to the existing proof to get Inv(v')!
    assert Inv(v') by {
      // FIXME: fill in here (solution: 1 line)
      TwoPCInvariantProof.InvInductive(v, v', event);
      // END EDIT
    }

    // The "new" part of this proof is to explain which AtomicCommit
    // (spec-level) action happened in response to each 2PC (protocol-level)
    // action. So the general strategy is: use skolemization (var :|) to "learn"
    // which thing happened in the DistributedSystem, split the cases, and
    // assert the right AtomicCommit.NextStep() predicate. Mostly, Dafny needs
    // those asserts because they're witnesses to the `exists` in AtomicCommit.Next().
    // FIXME: fill in here (solution: 51 lines)
    var step :| DistributedSystem.NextStep(v, v', event, step);
    assert step.HostActionStep?;
    var hostId := step.hostId;
    var msgOps := step.msgOps;

    if v.hosts[hostId].ParticipantVariables? {
      var pv, pv' := ParticipantVars(v, hostId), ParticipantVars(v', hostId);
      var av, av' := VariablesAbstraction(v), VariablesAbstraction(v');
      var astep := AtomicCommit.LearnDecisionStep(hostId);  // the only step that can happen
      var pstep :| ParticipantHost.NextStep(pv, pv', pstep, msgOps, event);

      match pstep
      case VoteStep =>
        if pv.decision.None? && pv.c.preference.No? {
          assert av.preferences[hostId] == No;
          assert AtomicCommit.NextStep(av, av', event, astep);
        }

      case LearnDecisionStep =>
        if pv.decision.None? && pv'.decision == Some(Abort) {
          var idx :| 0 <= idx < ParticipantCount(v) &&
                     ParticipantVars(v, idx).c.preference == No;
          assert av'.preferences[idx] == No;
          assert AtomicCommit.UltimateDecision(av'.preferences) == Abort;
          assert AtomicCommit.NextStep(av, av', event, astep);
        } else if pv.decision.None? && pv'.decision == Some(Commit) {
          assert AtomicCommit.NextStep(av, av', event, astep);
        }

    } else {
      assert event == NoOpEvent;
    }
    // END EDIT
  }
}