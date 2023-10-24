// Two Phase Commit Safety Proof
// Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  ghost predicate DecisionMsgsAgreeWithDecision(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 5 lines)
    && (CommitMsg(Commit) in v.network.sentMsgs ==> CoordinatorVars(v).decision == Some(Commit))
    && (CommitMsg(Abort) in v.network.sentMsgs ==> CoordinatorVars(v).decision == Some(Abort))
       // END EDIT
  }

  // We use this block of code to define additional invariants. We recommend you
  // define predicates for the individual parts of your invariant, to make
  // debugging easier.
  // FIXME: fill in here (solution: 20 lines)

  // 1. the decision of participant implies commit message sent
  ghost predicate ParticipantRecordDecision(v: Variables)
    requires v.WF()
  {
    && (forall i : nat |
          && ValidParticipantId(v, i)
          && ParticipantVars(v, i).decision == Some(Commit)
          :: CommitMsg(Commit) in v.network.sentMsgs)
    && (forall i : nat |
          && ValidParticipantId(v, i)
          && ParticipantVars(v, i).decision == Some(Abort)
          :: CommitMsg(Abort) in v.network.sentMsgs)
  }

  // 2. commit message sent the decision of the coordinator
  // See DecisionMsgsAgreeWithDecision

  // 3.the decision of the coordinator implies the record of the votes
  ghost predicate CoordinatorMakesDecision(v: Variables)
    requires v.WF()
  {
    && (CoordinatorVars(v).decision == Some(Commit) ==>
          forall i : nat | ValidParticipantId(v, i) ::
            CoordinatorVars(v).votes[i] == Some(Yes))
    && (CoordinatorVars(v).decision == Some(Abort) ==>
          exists i : nat | ValidParticipantId(v, i) ::
            CoordinatorVars(v).votes[i] == Some(No))
  }

  // 4. the record of the votes implies the vote message sent
  ghost predicate CoordinatorRecordsVotes(v: Variables)
    requires v.WF()
  {
    forall i : nat | ValidParticipantId(v, i) ::
      && (CoordinatorVars(v).votes[i] == Some(Yes) ==> VoteMsg(i, Yes) in v.network.sentMsgs)
      && (CoordinatorVars(v).votes[i] == Some(No) ==> VoteMsg(i, No) in v.network.sentMsgs)
  }

  // 5. the vote message sent implies the preference of the participant
  ghost predicate ParticipantSendVote(v: Variables)
    requires v.WF()
  {
    forall i : nat | ValidParticipantId(v, i) ::
      && (VoteMsg(i, Yes) in v.network.sentMsgs ==> ParticipantVars(v, i).c.preference == Yes)
      && (VoteMsg(i, No) in v.network.sentMsgs ==> ParticipantVars(v, i).c.preference == No)
  }
  // END EDIT


  ghost predicate Inv(v: Variables)
  {
    && v.WF()
       // FIXME: fill in here (solution: 2 lines)
    && CoordinatorMakesDecision(v)
    && CoordinatorRecordsVotes(v)
    && ParticipantSendVote(v)
    && ParticipantRecordDecision(v)
       // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(v)
       // ...but you'll need more.
    && Safety(v)
  }

  lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    // FIXME: fill in here (solution: 3 lines)
    assert CoordinatorMakesDecision(v);
    assert CoordinatorRecordsVotes(v);
    assert ParticipantSendVote(v);
    assert ParticipantRecordDecision(v);
    assert DecisionMsgsAgreeWithDecision(v);
    assert SafetyAC1(v);
    assert SafetyAC3(v);
    assert SafetyAC4(v);
    // END EDIT
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
  {
    //(not all of the below but much of it)
    // FIXME: fill in here (solution: 59 lines)
    assert ParticipantSendVote(v');
    assert CoordinatorRecordsVotes(v');
    assert CoordinatorMakesDecision(v');
    assert DecisionMsgsAgreeWithDecision(v');
    assert ParticipantRecordDecision(v');


    forall i : HostId |
      && ValidParticipantId(v', i)
      && ParticipantVars(v', i).decision != None
      ensures ParticipantVars(v', i).decision == CoordinatorVars(v').decision
    {
      match ParticipantVars(v', i).decision {
        case Some(Commit) => {
          assert ParticipantVars(v', i).c.preference == Yes;
          assert CoordinatorVars(v').votes[i] == Some(Yes);
          assert CoordinatorVars(v').decision == Some(Commit);
        }
        case Some(Abort) => {
          assert CommitMsg(Abort) in v'.network.sentMsgs;
          assert CoordinatorVars(v').decision == Some(Abort);
        }
      }
    }
    assert SafetyAC1(v');

    assert SafetyAC3(v');

    match CoordinatorVars(v').decision {
      case Some(Commit) => {
        assert CoordinatorVars(v').decision == Some(Commit);
        assert SafetyAC4(v');
      }
      case Some(Abort) => {
        assert CoordinatorVars(v').decision == Some(Abort);
        assert exists i : HostId | ValidParticipantId(v', i) :: CoordinatorVars(v').votes[i] == Some(No);
        assert SafetyAC4(v');
      }
      case None => {
        assert CoordinatorVars(v').decision == None;
        assert SafetyAC4(v');
      }
    }
    // END EDIT
  }

  lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
