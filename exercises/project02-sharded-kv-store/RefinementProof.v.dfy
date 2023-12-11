include "IMapHelpers.t.dfy"
include "RefinementObligation.t.dfy"

module RefinementProof refines RefinementObligation {
  import opened IMapHelpers
  import opened MessageType

  // We give you a strategy for an abstraction relation, turn it into an
  // abstraction function, and give you a few predicate to use in assembling
  // your invariant. This help is because some strategies for doing this proof
  // will result in a huge mess of invariants and/or serious issues with
  // verification performance, and we don't want you to go through that.

  // The strategy consists at a high level of showing that at each point in
  // time, every key has an "owner" that maps it to the correct value. A key can
  // either be owned by a host, or by a message in the network; if it's in the
  // network, clients can't request it until that message is delivered.

  datatype MapOwner = HostOwner(id: HostId) | MessageOwner(msg: Message)

  // OwnerValue should say that k maps to val specifically due to the owner o.
  ghost predicate OwnerValue(v: Variables, o: MapOwner, k: int, val: int)
    requires v.WF()
  {
    match o {
      case HostOwner(id) =>
        // What does it mean for host id to own a key (and assign it the value
        // val)?
        // FIXME: fill in here (solution: 3 lines)
        && v.ValidHost(id)
        && k in v.hosts[id].m
        && v.hosts[id].m[k] == val
      // END EDIT
      case MessageOwner(msg) =>
        // What does it mean for the network to own a key (and assign it the
        // value val)? This is a new concept relative to the atomic demo from
        // chapter06.
        // FIXME: fill in here (solution: 3 lines)
        && msg in v.network.inFlightMessages
        && msg.key == k
        && msg.value == val
           // END EDIT
    }
  }

  ghost predicate AbstractionRelation(v: Variables, av: AtomicKV.Variables)
  {
    && v.WF()
    && IsFull(av.table)
       // Use OwnerValue to connect v to av
       // FIXME: fill in here (solution: 1 line)
    && (forall k, val | (exists o :: OwnerValue(v, o, k, val)) :: av.table[k] == val)
       // END EDIT
  }

  /* Now we give you a library of some predicates to write your invariant. These
   * are made {:opaque}, which means you have to be intentional about how you use
   * them and prove them. Feel free to use `reveal OwnerHasSomeValue` for
   * example, but do so locally within an `assert P by { ... }` or `forall x ::
   * P(x) ensures { ... }` so that the definition isn't visible for the whole
   * proof - that will lead to timeouts and you'll have a Bad Time. */

  // This is a Dafny subset type - it's an imap that is known to be full
  type Owners = m:imap<int, MapOwner> | (forall k | IsKey(k) :: k in m)
    ghost witness imap k :: HostOwner(0)

  ghost predicate {:opaque} OwnerHasSomeValue(v: Variables, owner: Owners)
    requires v.WF()
  {
    && forall k | IsKey(k) :: exists val :: OwnerValue(v, owner[k], k, val)
  }

  ghost predicate {:opaque} OwnersDistinct(v: Variables, k: int)
    requires v.WF()
  {
    forall o1: MapOwner, o2: MapOwner, val1: int, val2: int ::
      (OwnerValue(v, o1, k, val1) && OwnerValue(v, o2, k, val2)) ==>
        o1 == o2 && val1 == val2
  }

  lemma use_OwnerHasSomeValue(v: Variables, owner: Owners, k: int) returns (val: int)
    requires v.WF()
    requires OwnerHasSomeValue(v, owner)
    ensures OwnerValue(v, owner[k], k, val)
  {
    assert IsKey(k);
    reveal OwnerHasSomeValue();
    val :| OwnerValue(v, owner[k], k, val);
  }

  lemma use_OwnersDistinct(v: Variables, k: int, o1: MapOwner, val1: int, o2: MapOwner, val2: int)
    requires v.WF()
    requires OwnersDistinct(v, k)
    requires OwnerValue(v, o1, k, val1)
    requires OwnerValue(v, o2, k, val2)
    ensures o1 == o2 && val1 == val2
  {
    assert IsKey(k);
    reveal OwnersDistinct();
  }

  // If o owns some value, it is the owner. This is a useful way to use
  // OwnersDistinct without fully revealing it.
  lemma use_OwnerValue(v: Variables, owners: Owners, o: MapOwner, k: int, val: int)
    requires v.WF()
    requires OwnerHasSomeValue(v, owners)
    requires OwnersDistinct(v, k)
    requires OwnerValue(v, o, k, val)
    ensures owners[k] == o
  {
    var val' := use_OwnerHasSomeValue(v, owners, k);
    reveal OwnersDistinct();
  }

  // We give you the abstraction function, which just uses a trick to turn the
  // relation into a function.
  ghost function VariablesAbstraction(v: Variables) : AtomicKV.Variables
  {
    if exists av :: AbstractionRelation(v, av) then
      var av :| AbstractionRelation(v, av); av
    else AtomicKV.Variables(EmptyMap())
  }

  lemma imap_ext_eq(m1: imap<int, int>, m2: imap<int, int>)
    requires IsFull(m1) && IsFull(m2)
    requires forall k: int :: m1[k] == m2[k]
    ensures m1 == m2
  {}

  lemma UniqueAbstraction(v: Variables, av: AtomicKV.Variables, owners: Owners)
    requires AbstractionRelation(v, av)
    requires OwnerHasSomeValue(v, owners)
    ensures VariablesAbstraction(v) == av
  {
    forall k:int
      ensures VariablesAbstraction(v).table[k] == av.table[k]
    {
      var val := use_OwnerHasSomeValue(v, owners, k);
    }
    // NOTE: this had to be factored into a lemma to work
    imap_ext_eq(VariablesAbstraction(v).table, av.table);
  }

  ghost predicate Inv(v: Variables)
  {
    // FIXME: fill in here (solution: 3 lines)
    && v.WF()
    && (forall k | IsKey(k) :: OwnersDistinct(v, k))
    && (exists owners :: OwnerHasSomeValue(v, owners))
       // END EDIT
  }

  ////////////////////////////////////////////////////////////////////////////


  lemma RefinementInit(v: Variables)
    //requires Init(v) // inherited from abstract module
    ensures Inv(v)
    ensures AtomicKV.Init(VariablesAbstraction(v))
  {
    // FIXME: fill in here (solution: 12 lines)
    assert forall k | IsKey(k) :: OwnersDistinct(v, k) by {
      reveal OwnersDistinct();
    }

    var owners := imap k | IsKey(k) :: HostOwner(0);
    assert OwnerHasSomeValue(v, owners) by {
      assert forall k | IsKey(k) :: OwnerValue(v, HostOwner(0), k, 0);
      reveal OwnerHasSomeValue();
    }

    var av := VariablesAbstraction(v);
    assert AtomicKV.Init(av) by {
      assert AbstractionRelation(v, AtomicKV.Variables(table := ZeroMap()));
      forall k | IsKey(k) ensures av.table[k] == 0 {
        assert OwnerValue(v, HostOwner(0), k, 0);
      }
      imap_ext_eq(av.table, ZeroMap());
    }
    // END EDIT
  }

  // FIXME: fill in here (solution: 204 lines)
  // Your proof goes here. We highly, highly recommend stating and proving a
  // refinement lemma for each step; see the chapter06 demo if you need help
  // structuring that.
  lemma OpPreservesOwnerHasSomeValue(v: Variables, v': Variables, id: HostId, msgOps: Network.MessageOps, event: Event, step: Host.Step)
    requires Inv(v)
    requires Next(v, v', event)
    requires v.ValidHost(id)
    requires Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step)
    requires exists dsstep :: NextStep(v, v', event, dsstep) && msgOps == dsstep.msgOps
    ensures exists owners :: OwnerHasSomeValue(v', owners)
  {
    var owner := if step.SendStep? then MessageOwner(msgOps.send.value) else HostOwner(id);
    var oldOwners :| OwnerHasSomeValue(v, oldOwners);
    var newOwners := oldOwners[step.key := owner];
    assert OwnerHasSomeValue(v', newOwners) by {
      forall k | IsKey(k) ensures exists val :: OwnerValue(v', newOwners[k], k, val) {
        if (k == step.key) {
          assert OwnerValue(v', owner, k, step.value);
        } else {
          var oldVal := use_OwnerHasSomeValue(v, oldOwners, k);
          assert OwnerValue(v', newOwners[k], k, oldVal);
        }
      }
      reveal OwnerHasSomeValue();
    }
  }

  lemma OpPerservesOwnersDistinctForOtherKeys(v: Variables, v': Variables, id: HostId, msgOps: Network.MessageOps, event: Event, step: Host.Step)
    requires Inv(v)
    requires Next(v, v', event)
    requires v.ValidHost(id)
    requires Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step)
    requires exists dsstep :: NextStep(v, v', event, dsstep) && msgOps == dsstep.msgOps
    ensures forall k | k != step.key :: OwnersDistinct(v', k)
  {
    forall k | k != step.key ensures OwnersDistinct(v', k) {
      forall o1: MapOwner, o2: MapOwner, val1: int, val2: int
        | OwnerValue(v', o1, k, val1) && OwnerValue(v', o2, k, val2)
        ensures o1 == o2 && val1 == val2 {
        use_OwnersDistinct(v, k, o1, val1, o2, val2);
      }
      reveal OwnersDistinct();
    }
  }

  ghost function GetValue(v: Variables, k: int) : int
    requires Inv(v)
  {
    reveal OwnerHasSomeValue();
    var val :| exists owner :: OwnerValue(v, owner, k, val);
    val
  }

  lemma InvImpliesFull(v: Variables)
    requires Inv(v)
    ensures IsFull(VariablesAbstraction(v).table)
  {
    reveal OwnersDistinct();

    var av := AtomicKV.Variables(table := imap k :: GetValue(v, k));
    forall k, val, o | OwnerValue(v, o, k, val) ensures av.table[k] == val {
      var owners : Owners :| OwnerHasSomeValue(v, owners);
      use_OwnerValue(v, owners, o, k, val);
    }
    assert AbstractionRelation(v, av);
  }

  lemma OpPerservesValueForOtherKeys(v: Variables, v': Variables, id: HostId, msgOps: Network.MessageOps, event: Event, step: Host.Step)
    requires Inv(v) && Inv(v')
    requires Next(v, v', event)
    requires v.ValidHost(id)
    requires Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step)
    requires exists dsstep :: NextStep(v, v', event, dsstep) && msgOps == dsstep.msgOps
    ensures IsFull(VariablesAbstraction(v).table)
    ensures IsFull(VariablesAbstraction(v').table)
    ensures forall k | k != step.key :: VariablesAbstraction(v).table[k] == VariablesAbstraction(v').table[k]
  {
    InvImpliesFull(v);
    InvImpliesFull(v');

    var av := VariablesAbstraction(v);
    var av' := VariablesAbstraction(v');
    forall k | k in av.table + av'.table && k != step.key ensures av.table[k] == av'.table[k] {
      var owners : Owners :| OwnerHasSomeValue(v, owners);
      var val := use_OwnerHasSomeValue(v, owners, k);
      assert OwnerValue(v', owners[k], k, val);
    }
  }

  lemma GetPreservesInvAndRefines(v: Variables, v': Variables, id: HostId, msgOps: Network.MessageOps, event: Event, step: Host.Step)
    requires Inv(v)
    requires Next(v, v', event)
    requires v.ValidHost(id)
    requires Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step)
    requires step.GetStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    assert v == v';
    OpPerservesValueForOtherKeys(v, v', id, msgOps, event, step);
    assert OwnerValue(v, HostOwner(id), step.key, step.value);
  }

  lemma PutPreservesInvAndRefines(v: Variables, v': Variables, id: HostId, msgOps: Network.MessageOps, event: Event, step: Host.Step)
    requires Inv(v)
    requires Next(v, v', event)
    requires v.ValidHost(id)
    requires Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step)
    requires step.PutStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    OpPerservesOwnersDistinctForOtherKeys(v, v', id, msgOps, event, step);
    OpPreservesOwnerHasSomeValue(v, v', id, msgOps, event, step);

    assert OwnersDistinct(v', step.key) by {
      forall o: MapOwner, val: int | OwnerValue(v', o, step.key, val)
        ensures o == HostOwner(id) && val == step.value {
        match o {
          case MessageOwner(msg') =>
            use_OwnersDistinct(v, step.key, HostOwner(id), v.hosts[id].m[step.key], MessageOwner(msg'), msg'.value);
            assert false;
          case HostOwner(id') =>
            use_OwnersDistinct(v, step.key, HostOwner(id), v.hosts[id].m[step.key], HostOwner(id'), v.hosts[id'].m[step.key]);
        }
      }
      reveal OwnersDistinct();
    }

    assert AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event) by {
      OpPerservesValueForOtherKeys(v, v', id, msgOps, event, step);
      assert OwnerValue(v', HostOwner(id), step.key, step.value);
    }
  }

  lemma SendPreservesInvAndRefines(v: Variables, v': Variables, id: HostId, msgOps: Network.MessageOps, event: Event, step: Host.Step)
    requires Inv(v)
    requires Next(v, v', event)
    requires v.ValidHost(id)
    requires Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step)
    requires exists dsstep :: NextStep(v, v', event, dsstep) && msgOps == dsstep.msgOps
    requires step.SendStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    OpPerservesOwnersDistinctForOtherKeys(v, v', id, msgOps, event, step);
    OpPreservesOwnerHasSomeValue(v, v', id, msgOps, event, step);

    assert OwnersDistinct(v', step.key) by {
      forall o: MapOwner, val: int | OwnerValue(v', o, step.key, val)
        ensures o == MessageOwner(msgOps.send.value) && val == step.value {
        match o {
          case MessageOwner(msg') =>
            if (msg'.value != step.value) {
              use_OwnersDistinct(v, step.key, HostOwner(id), v.hosts[id].m[step.key], MessageOwner(msg'), msg'.value);
              assert false;
            }
          case HostOwner(id') =>
            use_OwnersDistinct(v, step.key, HostOwner(id), v.hosts[id].m[step.key], HostOwner(id'), v.hosts[id'].m[step.key]);
            assert false;
        }
      }
      reveal OwnersDistinct();
    }

    assert AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event) by {
      OpPerservesValueForOtherKeys(v, v', id, msgOps, event, step);
      assert OwnerValue(v, HostOwner(id), step.key, step.value);
      assert OwnerValue(v', MessageOwner(msgOps.send.value), step.key, step.value);
    }
  }

  lemma RecvPreservesInvAndRefines(v: Variables, v': Variables, id: HostId, msgOps: Network.MessageOps, event: Event, step: Host.Step)
    requires Inv(v)
    requires Next(v, v', event)
    requires v.ValidHost(id)
    requires Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step)
    requires exists dsstep :: NextStep(v, v', event, dsstep) && msgOps == dsstep.msgOps
    requires step.RecvStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    OpPerservesOwnersDistinctForOtherKeys(v, v', id, msgOps, event, step);
    OpPreservesOwnerHasSomeValue(v, v', id, msgOps, event, step);

    assert OwnersDistinct(v', step.key) by {
      forall o: MapOwner, val: int | OwnerValue(v', o, step.key, val)
        ensures o == HostOwner(id) && val == step.value {
        var msg := msgOps.recv.value;
        match o {
          case MessageOwner(msg') =>
            use_OwnersDistinct(v, step.key, MessageOwner(msg), msg.value, MessageOwner(msg'), msg'.value);
            assert false;
          case HostOwner(id') =>
            if (id' != id) {
              use_OwnersDistinct(v, step.key, MessageOwner(msg), msg.value, HostOwner(id'), v.hosts[id'].m[step.key]);
              assert false;
            }
        }
      }
      reveal OwnersDistinct();
    }

    assert AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event) by {
      OpPerservesValueForOtherKeys(v, v', id, msgOps, event, step);
      assert OwnerValue(v, MessageOwner(msgOps.recv.value), step.key, step.value);
      assert OwnerValue(v', HostOwner(id), step.key, step.value);
    }
  }
  // END EDIT

  lemma RefinementNext(v: Variables, v': Variables, event: Event)
    // These requires & ensures all come from RefinementObligations; repeating
    // them here as a nearby crib sheet.
    // requires Next(v, v')
    // requires Inv(v)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    var dsstep: Step :| NextStep(v, v', event, dsstep);
    var msgOps := dsstep.msgOps;
    var id := dsstep.hostId;
    assert Host.Next(v.hosts[id], v'.hosts[id], msgOps, event);
    var step: Host.Step :| Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step);
    // All the solution dos here is match on the step and call the lemma for
    // refinement of that step.
    // FIXME: fill in here (solution: 14 lines)
    match step {
      case GetStep(key, value) =>
        GetPreservesInvAndRefines(v, v', id, msgOps, event, step);
      case PutStep(key, value) =>
        PutPreservesInvAndRefines(v, v', id, msgOps, event, step);
      case SendStep(key, value) =>
        SendPreservesInvAndRefines(v, v', id, msgOps, event, step);
      case RecvStep(key, value) =>
        RecvPreservesInvAndRefines(v, v', id, msgOps, event, step);
    }
    // END EDIT
  }
}
