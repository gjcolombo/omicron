---- MODULE update ----
EXTENDS Integers, TLC

CONSTANT NULL, VMS, STARTER, UPDATERS
ASSUME VMS # {}
ASSUME UPDATERS # {}

(* --algorithm update {

(*
This algorithm describes a method for updating instance states using an
"instance update" saga that can run in an independent task.

# Background & status quo

This section talks about how instance state is managed today (11 March 2024).

First, some terminology:

- An "instance" is an object in the Oxide API that represents a single virtual
  machine. Instances can be stopped or running, and while running they can be
  migrated between sleds.
- A "VMM" is a single Propolis process on a compute sled that incarnates and
  runs a virtual machine defined by a specific instance.

Instances and VMMs are recorded in separate tables in CockroachDB. Each instance
has two columns (`active_propolis_id` and `destination_propolis_id`) that
contain foreign keys to (respectively) the current Propolis VMM that's running
the instance and to the Propolis VMM to which the control plane is trying to
migrate this responsibility.

When an instance is not running, Nexus manages its state by updating fields in
CockroachDB. Once an instance has an active VMM (i.e. its `active_propolis_id`
is not NULL), that VMM's state "passes through" to become the instance's state.

A running virtual machine's state can change either because of requests made
from the API ("control plane, please stop this instance") or because of events
that occur in the VM itself (e.g., the guest OS executing its shutdown
sequence). Regardless of their origin, state transitions reach Nexus through a
common notification mechanism:

- Sled agent maintains a "monitor" task for each running VMM that issues a
  long-polling "monitor state" call to the instance's Propolis process.
- When Propolis effects or observes a VM state change, it publishes this change
  to all long-polling callers.
- The monitor task picks up these changes, decides how they should affect the
  control plane's VMM state (and possibly its instance state; more on this
  below), and calls Nexus's `cpapi_instances_put` internal API to reflect these
  changes.
- Nexus's `notify_instance_updated` function decides what to do with this new
  state. Some state transitions are simple, transient state changes that don't
  stop the VMM (e.g. Running -> Rebooting -> Running). When a VMM halts,
  however (either because it shut down or it was migrated away from),
  `notify_instance_updated` must observe this and clean up any resources
  associated with that VMM.

In the live migration case in particular, the sled agents and Nexus must be very
careful to arrange instance state transitions (and their generation numbers) so
that instances end up in the right states (i.e., no updates are lost to an
incorrectly-outdated generation number) and so that VMM resources get cleaned up
correctly when VMMs shut down.

# Problems with this model

There are two common ways for the instance state machine to fall apart. They
are:

1. Instances can easily get "lost" or stuck in some state because sled agent
   and/or Propolis have stopped sending state notifications to Nexus. This can
   happen if:
   - Propolis panics
   - Propolis gets wedged while starting or stopping
   - Sled agent restarts and forgets about the Propolis zone
   - Some other unexpected condition or weather causes sled agent's Propolis
     monitoring task to exit
2. Nexus moves instanecs to the "Failed" state outside of the regular instance
   state machine and doesn't properly clean up VMMs when it does so
   - This is exacerbated by Nexus's eagerness to declare that an instance has
     failed

It's difficult to fix these problems in the current model. The one Nexus
function that drives an instance's state machine forward is accessible only
through an interface that requires updates instance and VMM state that only sled
agents know how to provide. This makes it difficult to invoke this function from
arbitrary places in Nexus. Moreover, the state machine is brittle and
complicated to reason about because it's split across multiple components.

# Design goals

This spec seeks to describe an algorithm that gives Nexus a single code path
that can bring an instance up to date with the latest states of its VMMs. This
code should run in a saga (to obviate the need for awkward sled agent-driven
retries) and should be reentrant (so that it can be safely scheduled from
anywhere, including from an RPW that ensures that instances are eventually made
consistent with their VMMs).

Once this mechanism is in place, it should be much easier to improve the rest of
the instance state machine and to extend it to deal with things like sled
expungement. If nothing else, the state machine should be much easier to
understand: sleds update VMM states (and only VMM states); Nexus updates
instance states based on those VMM states; and there's one Nexus code path to
deal with all this, such that (e.g.) force-stopping an instance or marking it as
Failed is merely a matter of driving its VMMs to the correct (terminal) states
and then reconciling the instance's state accordingly.

# The design

The general design described here works as follows:

- Sled agents deal only with VMM states, not with instance states. All
  sled-agent-to-Nexus updates change only the state of a specific VMM, not its
  instance.
- An instance's externally-visible state is now computed by Nexus *based on* its
  VMM states. VMM states are no longer passed directly through as instance
  states.
- Nexus has an "instance update" saga that:
  - Reads the current instance state and any linked VMM states in a single
    atomic database operation
  - Obtains the exclusive right to update the instance
  - Evaluates the VMM states to determine the posterior instance state
  - Cleans up any resources and updates any other services that need to know
    about this new state
  - Sets the new instance state (dropping the lock at the same time)
  - Schedules another iteration of itself if the instance or VMM state changed
    in some other way in the meantime
  This saga can be triggered by anyone at any time. This model assumes that it's
  backed by an RPW that executes it periodically even if no other notifications
  issue.

  Note that the saga only tries to acquire the instance update lock. If this
  fails, there is no guarantee that any prior updates have actually been written
  out yet.

# This specification

This spec describes the instance update saga and checks that several interesting
invariants and properties hold even when the saga is concurrently reentered and
even when an instance's VMM states change while the saga is in progress.

It's important to note what the spec *does not* model. In this case:

- The particulars of sled agent and its interactions with Propolis are not
  modeled; VMM state updates simply appear out of the ether.
- The logic for triggering update sagas (via RPW or other means) is not modeled;
  instead, it's presumed that an update saga will magically run eventually,
  somehow or another. Note that this entails that the model also doesn't
  guarantee that changed instances will update before a deadline.

The spec is very heavily annotated to try to make it as comprehensible as
possible to readers who haven't used TLA+, though it assumes some familiarity
with set notation, predicate logic, and set quantifiers. Some of the ASCII
representations used below are:

- /\ is Boolean AND, \/ is Boolean OR, ~ is Boolean NOT`
- => is Boolean implication: p => q is equivalent to (p \/ ~q)
- <=> is bidirectional implication: p <=> q is equivalent to
  (p /\ q) \/ (~p /\ ~q)
- \A is the universal quantifier
- \E is the existential quantifier
- Set operators: '\' is set difference; '\union' is (as you might guess) the
  set union (cup) operator; '\intersect' is not used in this spec

*)

\* Global variables accessible to any process in the model.
variables
    (*
    Models the relevant fields of an instance as they appear in CRDB:

    - gen: The generation number protecting the instance's state and its VMM IDs
    - state: The externally-visible state of the instance (i.e. what you'd get
      if you queried it from the API).
    - active: The ID of the active VMM, a member of the `VMS` set. This is a
      TLA+ "model value": model values are equal only to themselves, not to any
      other model value or any value of any other kind.
    - dest: The ID of the migration target VMM, if there is one.
    - updater: The ID of the updater process that currently has the right to
      update this instance. (See the update procedure for an explanation of why
      this kind of resource locking is thought to be legal.)

    TLA+ note: this is the syntax for a function whose domain is the terms
    "gen", "state", etc. Later we'll define an invariant that describes all
    the possible structs with this same domain and the sets of acceptable values
    in the range; this is how we type-check variables in our model.
    *)
    instance = [
        gen |-> 1,
        state |-> "stopped",
        active |-> NULL,
        dest |-> NULL,
        updater |-> NULL
    ];

    (*
    Models the states of VMMs:

    - state: The current state of this VMM.
    - mig_to: The ID of the VMM this VMM is trying to migrate to.
    - mig_from: The ID of the VMM this VMM is trying to migrate from.

    Note that the actual VMM table in CRDB doesn't contain this source/
    destination information; instead it is "stored" by the fact that a running
    migration target will connect to its migration source and run the Propolis
    live migration procedure. We keep the variables here so that the model knows
    when there's an active migration that it needs to try to simulate.

    `vms` is a two-leveled struct: the domain of the "outer" struct is the set
    VMS, and for each VM there's an inner struct containing our fields.
    *)
    vms = [v \in VMS |-> [
        state |-> NULL,
        mig_to |-> NULL,
        mig_from |-> NULL
    ]];

    \* The set of VMs that have a resource reservation. This starts out empty.
    vmReservations = {};

    (*
    A simplified version of OPTE V2P propagation: this stores the ID of the
    VM whose location was last written to the rack's OPTE V2P mapping
    endpoints. You can imagine this encompassing other networking state,
    Oximeter registrations, etc.--anything where parts of the system outside the
    instance state machine need to know which VMM is current for a given
    instance.
    *)
    v2p = NULL;

    (*
    A helper variable that's checked to determine whether the current active
    migration should succeed or fail. When the starter process begins a
    migration, it forks the model, creating one path where this value is FALSE
    and one where it is TRUE. This is only updated when a new migration begins,
    and migrations always happen one after another, so this value remains
    constant throughout any single migration.
    *)
    migrationSucceeds = FALSE;

define {

\* Updaters are symmetric with one another. Tell TLA+ this to shrink the state
\* space.
Symmetry == Permutations(UPDATERS)

\* The externally-visible states an instance can be in.
\*
\* In the real control plane, there are several more states than this.
\* We don't model them to avoid state space explosion. This is OK
\* because:
\*
\* - An instance that's Creating can never have an active VMM.
\* - An instance that's Destroyed must have been Stopped first, so we
\*   only need to check that the correct predicates are upheld when an
\*   instance moves to Stopped.
\* - The Rebooting state is transient and doesn't change anything about
\*   the instance other than the externally-reported state made visible to
\*   the API; in this model, we only care about checking invariants around
\*   things like resource allocation and networking state updates that don't
\*   change when an instance reboots or begins to stop.
InstanceStates == {
    "starting",
    "running",
    "migrating",
    "stopping",
    "stopped"
}

\* The set of valid values for the `instance` variable: the generation number
\* must be an integer, the state must be in the set InstanceStates, etc.
InstanceType == instance \in [
    gen: Int,
    state: InstanceStates,
    active: VMS \union {NULL},
    dest: VMS \union {NULL},
    updater: UPDATERS \union {NULL}
]

\* The set of VMM states that we care to model. As with instances, we neglect
\* the Rebooting and Stopping states because they are transient and don't
\* affect the lifetimes of any VM resource reservations.
VmStates == {
    \* This VMM hasn't even been created yet.
    NULL,
    \* This VMM has been created but not necessarily handed off to its sled
    \* agent yet.
    \*
    \* Note that this state is not used in today's code. It's used in this
    \* design to provide a hint to the update saga that a VMM may still be
    \* removed by an in-doubt start or migrate saga.
    "creating",
    \* This VMM has been handed off to its sled agent but hasn't fully
    \* booted yet.
    "starting",
    \* This VMM is part a live migration.
    "migrating",
    \* This VMM is running.
    "running",
    \* This VMM has halted but its resources have not been released yet.
    "stopped",
    \* This VMM's resources are released. (This is distinct from Stopped
    \* in that in the Stopped state, the guest is not running, but the
    \* sled resources needed to run it are still allocated.)
    "destroyed"
}

(*
A type invariant for VMs: the `vms` variable must be in the set of functions
mapping each VM in VMS to another function where the state is in VmStates and
mig_to/mig_from are either NULL or in the set of VMs.
*)
VmType == vms \in [VMS -> [
    state: VmStates,
    mig_to: VMS \union {NULL},
    mig_from: VMS \union {NULL}
]]

\* Specifies the externally-visible instance state for an instance whose
\* active VM is in state `s`.
VmToInstanceState(s) ==
    CASE (s = "creating") -> "starting"
      [] (s = "starting") -> "starting"
      [] (s = "running") -> "running"
      [] (s = "migrating") -> "migrating"
      [] (s = "stopped") -> "stopping"
      [] (s = "destroyed") -> "stopping"

\* VMs must have resources allocated to themselves while they're in one of
\* these states.
VmResourceStates == {
    "starting",
    "running",
    "stopped"
}

\* Helper invariant to make sure that the "resources required" states are
\* VM states.
VmResourceStatesInVmStates == VmResourceStates \subseteq VmStates

(*
 * Operators. These are like "functions" in the programming-language sense: they
 * can take arguments and "return" values (but they are not multi-step
 * procedures).
 *)

\* Convenience operator for referring to the current state of VM `v`.
VmState(v) == vms[v].state

\* TRUE if all processes in the model have finished.
AllDone == \A p \in DOMAIN pc: pc[p] = "Done"

\* The set of VMs that haven't yet had any state set yet. The model uses this
\* to tweak the behavior of the last VM to stop: if a VM is about to stop but
\* sees that there are no successor VMs in the pool, it will fork execution to
\* create a timeline where it continues to run and a timeline where it stops.
UnusedVms == {v \in VMS: VmState(v) = NULL}

\* TRUE if all of the VMs have reached the end of their state machines and the
\* "VM starter" process has finished. (See below for more about the processes
\* in this model.)
StarterAndVmsDone ==
    /\ \A v \in VMS: pc[v] = "Done"
    /\ pc[STARTER] = "Done"

\* TRUE if an atomic read of the instance's current state and its VMMs' current
\* states should lead the state reader to conclude that the instance's state
\* needs to be updated.
\*
\* IMPORTANT: This operator is not a mere utility operator! It describes the
\* logic Nexus will actually use to determine whether an instance is out-of-date
\* and needs to be updated.
InstanceNeedsUpdate ==
    \/ /\ instance.active # NULL
       /\ \/ VmState(instance.active) = "destroyed"
          \/ VmToInstanceState(VmState(instance.active)) # instance.state

(*
Invariants and properties.

Invariants are predicates that hold in every state. Properties describe
temporal relationships between states.

Properties are much more expensive to check than invariants (and you can't use
symmetry sets with them). If you're running the model checker, you can
enable/disable specific checks in the model configuration file (update.cfg).
*)

\* Invariant: if a VM is in the migrating state, either its migrate-to or
\* migrate-from fields should be set.
MigrationRequiresPartner == \A v \in VMS:
    (VmState(v) = "migrating") => (vms[v].mig_to # NULL \/ vms[v].mig_from # NULL)

\* Invariant: a VM should either be migrating out or migrating in, but not
\* both at once.
OnlyOneMigrationPerVm == \A v \in VMS:
    /\ ((vms[v].mig_to # NULL) => (vms[v].mig_from = NULL))
    /\ ((vms[v].mig_from # NULL) => (vms[v].mig_to = NULL))

\* Invariant: if a VM is in a state that lets it consume resources on
\* a sled, it needs to have a resource entry. Note that the converse is
\* not necessarily true: it's OK for a stopped VM to have a reservation
\* for a while, though it does need to get cleaned up eventually (see below).
ActiveVmsHaveResources == \A v \in VMS:
    (VmState(v) \in VmResourceStates) => v \in vmReservations

\* Invariant: the instance should only go to the Stopped state if it
\* doesn't have an active VM, and if the instance record has no
\* living VMs it should go to the stopped state.
StoppedInstanceHasNoVms ==
    (instance.state = "stopped") <=>
        /\ instance.active = NULL
        /\ instance.dest = NULL

\* Invariant: if the instance is migrating to a destination then it
\* needs an active source.
MigrationRequiresActiveVm ==
    instance.dest # NULL => instance.active # NULL

\* Property: if the updater lock is owned in some state, then in the next state
\* either the lock is not owned or the updater is unchanged.
UpdaterLockNotStolen ==
    [][instance.updater # NULL => instance.updater' = NULL]_(instance.updater)

\* Property: the migration target always goes to NULL after being set
\* before being set to something else.
MigrationTargetNotStolen ==
    [][instance.dest # NULL => instance.dest' = NULL]_(instance.dest)

\* Property: it is eventually always the case that the V2P mapping
\* points to the active VMM. (Here the '<>' is the 'eventually' temporal
\* operator, and '[]' is the 'always' operator. This property holds iff,
\* in every execution, the predicate "v2p = instance.active" becomes true
\* and stays true for the remainder of the execution.)
OpteMappingsEventuallyConsistent ==
    <>[](v2p = instance.active)

\* An invariant version of the previous property: once the system is quiesced,
\* the V2P mapping should point to the instance's active VMM (or to NULL if
\* no VMM is active).
OpteMappingsConsistentAtEnd == AllDone => v2p = instance.active

\* Property: once a VM reaches the destroyed state, it stays there.
DestroyedVmsStayDestroyed ==
    [][\A v \in VMS:
        vms[v].state = "destroyed" => vms'[v].state = "destroyed"]_vms

\* Property: once a VM reaches the destroyed state, its reservation
\* eventually gets deleted and stays deleted. Here the `~>` operator represents
\* eventual implication: if the VM state goes to destroyed, then in some future
\* state, it begins always to be the case that the VM has no resource
\* reservation.
DestroyedVmsGetFreed ==
    \A v \in VMS:
        (VmState(v) = "destroyed" ~> [](v \notin vmReservations))

\* An invariant version of the previous property: once the system is quiesced,
\* all VMs must be destroyed, except for the active VM, which must be running
\* if it exists.
VmsFreeAtEnd == AllDone => \A v \in VMS:
    \/ VmState(v) = "destroyed"
    \/ /\ instance.active = v
       /\ VmState(v) = "running"

\* Property: if the instance has a migration target, then in some future state
\* it does not have a migration target.
MigrationsEventuallyResolve ==
    instance.dest # NULL ~> instance.dest = NULL

\* An invariant version of the previous property: when all processes have
\* quiesced there should not be a migration target.
MigrationsResolveAtEnd == AllDone => instance.dest = NULL
}

(*
This is the collection of update sagas, one for each member of UPDATERS.

This process, like the others in this model, is weakly fair. By default, TLA+
models are allowed to stutter, i.e. to take *no* action at a particular
execution step (even if a valid action exists). A weakly-fair state transition
(or set of transitions) is one where, if the transition is eventually always
possible, the transition is forced to occur. (By contrast, strong fairness
guarantees that if a transition is always eventually possible--that is, it is
possible in one state, then isn't possible in the next, but then becomes
possible again, etc.--then it will eventually occur.)

We assume weak fairness for all processes in this model. Here this means we're
assuming all sagas eventually run to completion, even if their executors crash
sometimes. (If we run out of Nexuses we have bigger problems.)j
forward progress. This is not
*)
fair process (updater \in UPDATERS)
\* Local variables in each instance of this process.
variable readInstance, readVmState, readDestVmState;
{

(*
Each statement ending in a colon is a label that represents a single atomic step
in the model. That is, all of the statements and variable updates under a single
label are presumed to happen at a single instant in time.
*)
ReadFromCrdb:
    while (TRUE) {
        (*
        The 'await' keyword puts a guard on the execution of this step: the
        other actions in this step, and the transition to the next step, can
        occur only in states where the await condition is satisfied.

        Here we're modeling that, while a saga execution can kick off at any
        time (and might even read from CRDB), it will only actually end up doing
        anything if it turns out that (a) the instance looks like it needs to be
        updated, and (b) the instance lock is not currently held. Collapsing
        this check into the same step that reads the instance record and
        acquires the lock significantly reduces the number of states in the
        model.

        The 'StarterAndVmsDone' portion of the check lets all the updaters
        short-circuit when no more instance changes are forthcoming. This allows
        us to enable deadlock detection during model checking (it will fail if
        some processes don't explicitly reach their final implicit Done labels).
        *)
        await (InstanceNeedsUpdate /\ instance.updater = NULL) \/ StarterAndVmsDone;
        if (~InstanceNeedsUpdate) {
            goto Done;
        } else if (instance.updater = NULL) {
            (*
            The details of acquiring the lock are not modeled here. In the real
            saga, a saga step needs to

            - read the instance record and observe the lock
            - if not held, try to write back a new record where the current saga
              (identified by some UUID) holds the lock and the generation number
              is incremented
              - if writing back fails, repeat this process
            - if held by the current saga, continue
            - if already held by someone else, bail

            Since the 'await' guard already guaranteed that the lock wasn't held
            it's safe just to set the updater here.
            *)

            instance.updater := self;

            \* The rest of the saga operates on the instance and VMM states
            \* read in this step. Since all these assignments are under a single
            \* label, these must come from a single atomic DB read. (One joy
            \* of TLA+ is that we don't have to figure out what this query
            \* will actually look like!)
            readInstance := instance;
            readVmState := vms[instance.active].state;
            if (instance.dest # NULL) {
                readDestVmState := vms[instance.dest].state;
            } else {
                readDestVmState := NULL;
            };
        } else {
            goto ReadFromCrdb;
        };
    (*
    Deal with any active live migration. In this model the rule is that if the
    instance's active VMM is gone, but there's a migration target, the target
    becomes active right away irrespective of what its state is. The update
    procedure then cleans up the source's resources before committing the new
    instance state. The destination VMM's state is ignored for now--the next
    invocation of the update saga will take care of it.
    *)
    ResolveMigration:
        if (readVmState = "destroyed") {
            \* If there's no migration target, go down the conventional cleanup
            \* path below.
            if (readInstance.dest = NULL) {
                goto CleanRunningVmm;
            } else {
                \* Setting OPTE state and releasing resource reservations should
                \* probably be separate saga nodes, but we collapse them here
                \* to reduce the size of the state space, since the two effects
                \* are otherwise orthogonal.
                CleanSource:
                    v2p := readInstance.dest;
                    vmReservations := vmReservations \ {readInstance.active};
                \* Put back the new instance state. If the instance was updated
                \* in the meantime, just drop the lock and wait for the next
                \* updater to take care of it. (See below for more discussion.)
                EndMigration:
                    if (instance.gen = readInstance.gen) {
                        instance.gen := instance.gen + 1 ||
                        instance.active := readInstance.dest ||
                        instance.dest := NULL ||
                        instance.state := VmToInstanceState(readDestVmState) ||
                        instance.updater := NULL;
                    } else {
                        instance.updater := NULL;
                    };

                    goto ReadFromCrdb;
            };
        };

    (*
    As above, collapse all cleanup tasks into a single step to reduce the
    size of the model. In practice these are probably separate saga nodes.
    We do want this to happen in its own step to model possibly-overrunning
    instance state updates (e.g. if our instance update lock is missing or
    broken).
    *)
    CleanRunningVmm:
        if (readVmState = "destroyed") {
            v2p := NULL;
            vmReservations := vmReservations \ {readInstance.active};
        };
    (*
    Attempt to write back the new instance state and update the generation
    number. If this write fails, fall back to just dropping the update
    lock, on the presumption that the saga will run again later (in
    practice this saga could queue a new version of itself).

    We rely here on the fact that, once a VMM ID is set in an instance, there
    are only two ways to clear it: either the saga that set it can unwind, or
    this saga can remove it. If no start/migrate sagas unwind, the instance
    generation number eventually saturates: there are no places to install new
    VMM IDs, so the only thing that can update the instance generation number is
    an update saga.

    If start/migrate sagas do repeatedly unwind, it's possible that instance
    updaters will never break through and successfully change the instance's
    generation number. This doesn't happen in the model because we only
    start/migrate the instance a finite number of times. Nexus could avoid the
    infinite case in practice by, e.g., maintaining a count of the number of
    consecutive start/migrate requests that have failed and marking the instance
    as "faulted" (preventing new attempts) if this number gets too high.
    *)
    TryApplyUpdate:
        if (instance.gen = readInstance.gen) {
            if (readVmState = "destroyed") {
                instance.gen := instance.gen + 1 ||
                instance.active := NULL ||
                instance.state := "stopped" ||
                instance.updater := NULL;
            } else {
                instance.gen := instance.gen + 1 ||
                instance.state := VmToInstanceState(readVmState) ||
                instance.updater := NULL;
            };
        } else {
            instance.updater := NULL;
        }
    }
}

\* Advance VMs through the state machine. We're explicitly not modeling
\* any process for cleaning up if Nexus stops getting state updates for
\* a particular VM.
fair process (vm \in VMS) {
VmWaitToStart:
    \* VMs start out with a NULL state, which means no one has tried to start
    \* them yet. The starter process will move them to "creating" and then hand
    \* them over to either "starting" or "migrating" (successful sagas) or
    \* directly to "destroyed" (failed saga that unwound).
    await (VmState(self) \in {"starting", "migrating", "destroyed"});
    if (VmState(self) = "starting") {
        VmRunning:
            vms[self].state := "running";
        VmMigrateOrStop:
            \* If there's no migration target for this VM in this execution,
            \* just stop it. Otherwise, decide how to handle the migration.
            if (vms[self].mig_to = NULL) {
                vms[self].state := "stopped";
            } else {
                (*
                The either/or construct forks execution, creating one timeline
                for each branch. Here, we model both a "normal" migration where
                the destination contacts the source and the case where the
                source stops before the destination can reach it.
                *)
                either {
                    vms[self].state := "stopped";
                } or {
                    VmAcceptMigrationRequest:
                        vms[self].state := "migrating";
                    VmFinishSourceMigration:
                        \* Both these branches will be checked (a separate
                        \* timeline is created for both values of
                        \* migrationSucceeds for each migration).
                        if (migrationSucceeds) {
                            vms[self].state := "stopped" ||
                            vms[self].mig_to := NULL;
                        } else {
                            \* Migration failed; go back to Running and clear
                            \* `mig_to` so as not to try to migrate again.
                            vms[self].state := "running" ||
                            vms[self].mig_to := NULL;
                            goto VmMigrateOrStop;
                        };
                };
            };
    } else if (VmState(self) = "migrating") {
        VmSendMigrationRequest:
            assert(vms[self].mig_from # NULL);
            if (VmState(vms[self].mig_from) = "running") {
                vms[vms[self].mig_from].mig_to := self;
            } else {
                \* The source isn't alive anymore, so self-destruct.
                goto VmDestroyed;
            };
        VmFinishTargetMigration:
            if (migrationSucceeds) {
                vms[self].state := "running" ||
                vms[self].mig_from := NULL;
                goto VmMigrateOrStop;
            } else {
                vms[self].state := "stopped" ||
                vms[self].mig_from := NULL;
            };
    } else {
        assert(VmState(self) = "destroyed");
        goto Done;
    };

VmDestroyed:
    \* If this is the last incarnation of this VM, give it the choice of
    \* remaining in Running and getting shut down so that the model can
    \* check properties in both cases.
    if (UnusedVms = {} /\ VmState(self) = "running") {
        either {
            vms[self].state := "destroyed";
        } or {
            skip;
        };
    } else {
        vms[self].state := "destroyed";
    };
}

fair process (starter \in {STARTER})
variable vm, mig_from = NULL;
{
CreateVmm:
    while (UnusedVms # {}) {
        \* Once again, avoid state space explosion by waiting to activate this
        \* state until there is someplace to put a new VM.
        \*
        \* The model checker will check each possible timeline where this
        \* condition holds--i.e., it will exhaustively cover every possible
        \* point where a start/migrate request could validly begin.
        await
            \/ instance.active = NULL
            \/ /\ instance.active # NULL
               /\ instance.dest = NULL;

        \* Instead of forking the timeline here, just choose the next available
        \* VM from the set. CHOOSE...TRUE is deterministic, but that's OK here
        \* because all the VMs are equivalent anyway.
        vm := CHOOSE v \in UnusedVms: TRUE;

        \* Reserve space for the VM on a sled (if this fails then nothing else
        \* will happen anyway) and put it into the "extant but maybe not on a
        \* sled yet" state.
        vms[vm].state := "creating";
        vmReservations := vmReservations \union {vm};

        \* This is all modeled as an atomic operation, but will probably span
        \* multiple saga nodes in practice.
        if (instance.active = NULL) {
            instance.active := vm ||
            instance.gen := instance.gen + 1 ||
            instance.state := VmToInstanceState("creating");

            \* Model unwinding after pasting the VMM ID into the record as an
            \* immediate transition to "destroyed".
            either {
                SetOpte:
                    v2p := vm;
                StartVmm:
                    vms[vm].state := "starting";
            } or {
                FailStart:
                    instance.active := NULL ||
                    instance.gen := instance.gen + 1 ||
                    instance.state := "stopped";
                    vms[vm].state := "destroyed";
            }
        } else {
            \* The migration saga doesn't change the instance's effective state
            \* directly (since that update may conflict with a state change from
            \* the current active VM). Instead the "migrating" label is applied
            \* by the update task.
            instance.dest := vm ||
            instance.gen := instance.gen + 1;

            \* Ensuring the migration target Propolis happens in a separate
            \* step during which the instance's active VMM is allowed to
            \* change from what was captured here.
            mig_from := instance.active;
            MigrateVmm:
                \* The `with` statement creates one timeline for each value
                \* in the set.
                with (res \in BOOLEAN) {
                    migrationSucceeds := res;
                };
                vms[vm].mig_from := mig_from ||
                vms[vm].state := "migrating";
        };
    }
}

} *)
\* BEGIN TRANSLATION (chksum(pcal) = "c2e796c6" /\ chksum(tla) = "1ce953e8")
\* Process vm at line 651 col 6 changed to vm_
CONSTANT defaultInitValue
VARIABLES instance, vms, vmReservations, v2p, migrationSucceeds, pc

(* define statement *)
Symmetry == Permutations(UPDATERS)
















InstanceStates == {
    "starting",
    "running",
    "migrating",
    "stopping",
    "stopped"
}



InstanceType == instance \in [
    gen: Int,
    state: InstanceStates,
    active: VMS \union {NULL},
    dest: VMS \union {NULL},
    updater: UPDATERS \union {NULL}
]




VmStates == {

    NULL,






    "creating",


    "starting",

    "migrating",

    "running",

    "stopped",



    "destroyed"
}






VmType == vms \in [VMS -> [
    state: VmStates,
    mig_to: VMS \union {NULL},
    mig_from: VMS \union {NULL}
]]



VmToInstanceState(s) ==
    CASE (s = "creating") -> "starting"
      [] (s = "starting") -> "starting"
      [] (s = "running") -> "running"
      [] (s = "migrating") -> "migrating"
      [] (s = "stopped") -> "stopping"
      [] (s = "destroyed") -> "stopping"



VmResourceStates == {
    "starting",
    "running",
    "stopped"
}



VmResourceStatesInVmStates == VmResourceStates \subseteq VmStates








VmState(v) == vms[v].state


AllDone == \A p \in DOMAIN pc: pc[p] = "Done"





UnusedVms == {v \in VMS: VmState(v) = NULL}




StarterAndVmsDone ==
    /\ \A v \in VMS: pc[v] = "Done"
    /\ pc[STARTER] = "Done"








InstanceNeedsUpdate ==
    \/ /\ instance.active # NULL
       /\ \/ VmState(instance.active) = "destroyed"
          \/ VmToInstanceState(VmState(instance.active)) # instance.state














MigrationRequiresPartner == \A v \in VMS:
    (VmState(v) = "migrating") => (vms[v].mig_to # NULL \/ vms[v].mig_from # NULL)



OnlyOneMigrationPerVm == \A v \in VMS:
    /\ ((vms[v].mig_to # NULL) => (vms[v].mig_from = NULL))
    /\ ((vms[v].mig_from # NULL) => (vms[v].mig_to = NULL))





ActiveVmsHaveResources == \A v \in VMS:
    (VmState(v) \in VmResourceStates) => v \in vmReservations




StoppedInstanceHasNoVms ==
    (instance.state = "stopped") <=>
        /\ instance.active = NULL
        /\ instance.dest = NULL



MigrationRequiresActiveVm ==
    instance.dest # NULL => instance.active # NULL



UpdaterLockNotStolen ==
    [][instance.updater # NULL => instance.updater' = NULL]_(instance.updater)



MigrationTargetNotStolen ==
    [][instance.dest # NULL => instance.dest' = NULL]_(instance.dest)






OpteMappingsEventuallyConsistent ==
    <>[](v2p = instance.active)




OpteMappingsConsistentAtEnd == AllDone => v2p = instance.active


DestroyedVmsStayDestroyed ==
    [][\A v \in VMS:
        vms[v].state = "destroyed" => vms'[v].state = "destroyed"]_vms






DestroyedVmsGetFreed ==
    \A v \in VMS:
        (VmState(v) = "destroyed" ~> [](v \notin vmReservations))




VmsFreeAtEnd == AllDone => \A v \in VMS:
    \/ VmState(v) = "destroyed"
    \/ /\ instance.active = v
       /\ VmState(v) = "running"



MigrationsEventuallyResolve ==
    instance.dest # NULL ~> instance.dest = NULL



MigrationsResolveAtEnd == AllDone => instance.dest = NULL

VARIABLES readInstance, readVmState, readDestVmState, vm, mig_from

vars == << instance, vms, vmReservations, v2p, migrationSucceeds, pc, 
           readInstance, readVmState, readDestVmState, vm, mig_from >>

ProcSet == (UPDATERS) \cup (VMS) \cup ({STARTER})

Init == (* Global variables *)
        /\ instance =            [
                          gen |-> 1,
                          state |-> "stopped",
                          active |-> NULL,
                          dest |-> NULL,
                          updater |-> NULL
                      ]
        /\ vms =       [v \in VMS |-> [
                     state |-> NULL,
                     mig_to |-> NULL,
                     mig_from |-> NULL
                 ]]
        /\ vmReservations = {}
        /\ v2p = NULL
        /\ migrationSucceeds = FALSE
        (* Process updater *)
        /\ readInstance = [self \in UPDATERS |-> defaultInitValue]
        /\ readVmState = [self \in UPDATERS |-> defaultInitValue]
        /\ readDestVmState = [self \in UPDATERS |-> defaultInitValue]
        (* Process starter *)
        /\ vm = [self \in {STARTER} |-> defaultInitValue]
        /\ mig_from = [self \in {STARTER} |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in UPDATERS -> "ReadFromCrdb"
                                        [] self \in VMS -> "VmWaitToStart"
                                        [] self \in {STARTER} -> "CreateVmm"]

ReadFromCrdb(self) == /\ pc[self] = "ReadFromCrdb"
                      /\ (InstanceNeedsUpdate /\ instance.updater = NULL) \/ StarterAndVmsDone
                      /\ IF ~InstanceNeedsUpdate
                            THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << instance, readInstance, 
                                                 readVmState, readDestVmState >>
                            ELSE /\ IF instance.updater = NULL
                                       THEN /\ instance' = [instance EXCEPT !.updater = self]
                                            /\ readInstance' = [readInstance EXCEPT ![self] = instance']
                                            /\ readVmState' = [readVmState EXCEPT ![self] = vms[instance'.active].state]
                                            /\ IF instance'.dest # NULL
                                                  THEN /\ readDestVmState' = [readDestVmState EXCEPT ![self] = vms[instance'.dest].state]
                                                  ELSE /\ readDestVmState' = [readDestVmState EXCEPT ![self] = NULL]
                                            /\ pc' = [pc EXCEPT ![self] = "ResolveMigration"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ReadFromCrdb"]
                                            /\ UNCHANGED << instance, 
                                                            readInstance, 
                                                            readVmState, 
                                                            readDestVmState >>
                      /\ UNCHANGED << vms, vmReservations, v2p, 
                                      migrationSucceeds, vm, mig_from >>

ResolveMigration(self) == /\ pc[self] = "ResolveMigration"
                          /\ IF readVmState[self] = "destroyed"
                                THEN /\ IF readInstance[self].dest = NULL
                                           THEN /\ pc' = [pc EXCEPT ![self] = "CleanRunningVmm"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "CleanSource"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "CleanRunningVmm"]
                          /\ UNCHANGED << instance, vms, vmReservations, v2p, 
                                          migrationSucceeds, readInstance, 
                                          readVmState, readDestVmState, vm, 
                                          mig_from >>

CleanSource(self) == /\ pc[self] = "CleanSource"
                     /\ v2p' = readInstance[self].dest
                     /\ vmReservations' = vmReservations \ {readInstance[self].active}
                     /\ pc' = [pc EXCEPT ![self] = "EndMigration"]
                     /\ UNCHANGED << instance, vms, migrationSucceeds, 
                                     readInstance, readVmState, 
                                     readDestVmState, vm, mig_from >>

EndMigration(self) == /\ pc[self] = "EndMigration"
                      /\ IF instance.gen = readInstance[self].gen
                            THEN /\ instance' = [instance EXCEPT !.gen = instance.gen + 1,
                                                                 !.active = readInstance[self].dest,
                                                                 !.dest = NULL,
                                                                 !.state = VmToInstanceState(readDestVmState[self]),
                                                                 !.updater = NULL]
                            ELSE /\ instance' = [instance EXCEPT !.updater = NULL]
                      /\ pc' = [pc EXCEPT ![self] = "ReadFromCrdb"]
                      /\ UNCHANGED << vms, vmReservations, v2p, 
                                      migrationSucceeds, readInstance, 
                                      readVmState, readDestVmState, vm, 
                                      mig_from >>

CleanRunningVmm(self) == /\ pc[self] = "CleanRunningVmm"
                         /\ IF readVmState[self] = "destroyed"
                               THEN /\ v2p' = NULL
                                    /\ vmReservations' = vmReservations \ {readInstance[self].active}
                               ELSE /\ TRUE
                                    /\ UNCHANGED << vmReservations, v2p >>
                         /\ pc' = [pc EXCEPT ![self] = "TryApplyUpdate"]
                         /\ UNCHANGED << instance, vms, migrationSucceeds, 
                                         readInstance, readVmState, 
                                         readDestVmState, vm, mig_from >>

TryApplyUpdate(self) == /\ pc[self] = "TryApplyUpdate"
                        /\ IF instance.gen = readInstance[self].gen
                              THEN /\ IF readVmState[self] = "destroyed"
                                         THEN /\ instance' = [instance EXCEPT !.gen = instance.gen + 1,
                                                                              !.active = NULL,
                                                                              !.state = "stopped",
                                                                              !.updater = NULL]
                                         ELSE /\ instance' = [instance EXCEPT !.gen = instance.gen + 1,
                                                                              !.state = VmToInstanceState(readVmState[self]),
                                                                              !.updater = NULL]
                              ELSE /\ instance' = [instance EXCEPT !.updater = NULL]
                        /\ pc' = [pc EXCEPT ![self] = "ReadFromCrdb"]
                        /\ UNCHANGED << vms, vmReservations, v2p, 
                                        migrationSucceeds, readInstance, 
                                        readVmState, readDestVmState, vm, 
                                        mig_from >>

updater(self) == ReadFromCrdb(self) \/ ResolveMigration(self)
                    \/ CleanSource(self) \/ EndMigration(self)
                    \/ CleanRunningVmm(self) \/ TryApplyUpdate(self)

VmWaitToStart(self) == /\ pc[self] = "VmWaitToStart"
                       /\ (VmState(self) \in {"starting", "migrating", "destroyed"})
                       /\ IF VmState(self) = "starting"
                             THEN /\ pc' = [pc EXCEPT ![self] = "VmRunning"]
                             ELSE /\ IF VmState(self) = "migrating"
                                        THEN /\ pc' = [pc EXCEPT ![self] = "VmSendMigrationRequest"]
                                        ELSE /\ Assert((VmState(self) = "destroyed"), 
                                                       "Failure of assertion at line 713, column 9.")
                                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << instance, vms, vmReservations, v2p, 
                                       migrationSucceeds, readInstance, 
                                       readVmState, readDestVmState, vm, 
                                       mig_from >>

VmRunning(self) == /\ pc[self] = "VmRunning"
                   /\ vms' = [vms EXCEPT ![self].state = "running"]
                   /\ pc' = [pc EXCEPT ![self] = "VmMigrateOrStop"]
                   /\ UNCHANGED << instance, vmReservations, v2p, 
                                   migrationSucceeds, readInstance, 
                                   readVmState, readDestVmState, vm, mig_from >>

VmMigrateOrStop(self) == /\ pc[self] = "VmMigrateOrStop"
                         /\ IF vms[self].mig_to = NULL
                               THEN /\ vms' = [vms EXCEPT ![self].state = "stopped"]
                                    /\ pc' = [pc EXCEPT ![self] = "VmDestroyed"]
                               ELSE /\ \/ /\ vms' = [vms EXCEPT ![self].state = "stopped"]
                                          /\ pc' = [pc EXCEPT ![self] = "VmDestroyed"]
                                       \/ /\ pc' = [pc EXCEPT ![self] = "VmAcceptMigrationRequest"]
                                          /\ vms' = vms
                         /\ UNCHANGED << instance, vmReservations, v2p, 
                                         migrationSucceeds, readInstance, 
                                         readVmState, readDestVmState, vm, 
                                         mig_from >>

VmAcceptMigrationRequest(self) == /\ pc[self] = "VmAcceptMigrationRequest"
                                  /\ vms' = [vms EXCEPT ![self].state = "migrating"]
                                  /\ pc' = [pc EXCEPT ![self] = "VmFinishSourceMigration"]
                                  /\ UNCHANGED << instance, vmReservations, 
                                                  v2p, migrationSucceeds, 
                                                  readInstance, readVmState, 
                                                  readDestVmState, vm, 
                                                  mig_from >>

VmFinishSourceMigration(self) == /\ pc[self] = "VmFinishSourceMigration"
                                 /\ IF migrationSucceeds
                                       THEN /\ vms' = [vms EXCEPT ![self].state = "stopped",
                                                                  ![self].mig_to = NULL]
                                            /\ pc' = [pc EXCEPT ![self] = "VmDestroyed"]
                                       ELSE /\ vms' = [vms EXCEPT ![self].state = "running",
                                                                  ![self].mig_to = NULL]
                                            /\ pc' = [pc EXCEPT ![self] = "VmMigrateOrStop"]
                                 /\ UNCHANGED << instance, vmReservations, v2p, 
                                                 migrationSucceeds, 
                                                 readInstance, readVmState, 
                                                 readDestVmState, vm, mig_from >>

VmSendMigrationRequest(self) == /\ pc[self] = "VmSendMigrationRequest"
                                /\ Assert((vms[self].mig_from # NULL), 
                                          "Failure of assertion at line 696, column 13.")
                                /\ IF VmState(vms[self].mig_from) = "running"
                                      THEN /\ vms' = [vms EXCEPT ![vms[self].mig_from].mig_to = self]
                                           /\ pc' = [pc EXCEPT ![self] = "VmFinishTargetMigration"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "VmDestroyed"]
                                           /\ vms' = vms
                                /\ UNCHANGED << instance, vmReservations, v2p, 
                                                migrationSucceeds, 
                                                readInstance, readVmState, 
                                                readDestVmState, vm, mig_from >>

VmFinishTargetMigration(self) == /\ pc[self] = "VmFinishTargetMigration"
                                 /\ IF migrationSucceeds
                                       THEN /\ vms' = [vms EXCEPT ![self].state = "running",
                                                                  ![self].mig_from = NULL]
                                            /\ pc' = [pc EXCEPT ![self] = "VmMigrateOrStop"]
                                       ELSE /\ vms' = [vms EXCEPT ![self].state = "stopped",
                                                                  ![self].mig_from = NULL]
                                            /\ pc' = [pc EXCEPT ![self] = "VmDestroyed"]
                                 /\ UNCHANGED << instance, vmReservations, v2p, 
                                                 migrationSucceeds, 
                                                 readInstance, readVmState, 
                                                 readDestVmState, vm, mig_from >>

VmDestroyed(self) == /\ pc[self] = "VmDestroyed"
                     /\ IF UnusedVms = {} /\ VmState(self) = "running"
                           THEN /\ \/ /\ vms' = [vms EXCEPT ![self].state = "destroyed"]
                                   \/ /\ TRUE
                                      /\ vms' = vms
                           ELSE /\ vms' = [vms EXCEPT ![self].state = "destroyed"]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << instance, vmReservations, v2p, 
                                     migrationSucceeds, readInstance, 
                                     readVmState, readDestVmState, vm, 
                                     mig_from >>

vm_(self) == VmWaitToStart(self) \/ VmRunning(self)
                \/ VmMigrateOrStop(self) \/ VmAcceptMigrationRequest(self)
                \/ VmFinishSourceMigration(self)
                \/ VmSendMigrationRequest(self)
                \/ VmFinishTargetMigration(self) \/ VmDestroyed(self)

CreateVmm(self) == /\ pc[self] = "CreateVmm"
                   /\ IF UnusedVms # {}
                         THEN /\ \/ instance.active = NULL
                                 \/ /\ instance.active # NULL
                                    /\ instance.dest = NULL
                              /\ vm' = [vm EXCEPT ![self] = CHOOSE v \in UnusedVms: TRUE]
                              /\ vms' = [vms EXCEPT ![vm'[self]].state = "creating"]
                              /\ vmReservations' = (vmReservations \union {vm'[self]})
                              /\ IF instance.active = NULL
                                    THEN /\ instance' = [instance EXCEPT !.active = vm'[self],
                                                                         !.gen = instance.gen + 1,
                                                                         !.state = VmToInstanceState("creating")]
                                         /\ \/ /\ pc' = [pc EXCEPT ![self] = "SetOpte"]
                                            \/ /\ pc' = [pc EXCEPT ![self] = "FailStart"]
                                         /\ UNCHANGED mig_from
                                    ELSE /\ instance' = [instance EXCEPT !.dest = vm'[self],
                                                                         !.gen = instance.gen + 1]
                                         /\ mig_from' = [mig_from EXCEPT ![self] = instance'.active]
                                         /\ pc' = [pc EXCEPT ![self] = "MigrateVmm"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << instance, vms, vmReservations, 
                                              vm, mig_from >>
                   /\ UNCHANGED << v2p, migrationSucceeds, readInstance, 
                                   readVmState, readDestVmState >>

MigrateVmm(self) == /\ pc[self] = "MigrateVmm"
                    /\ \E res \in BOOLEAN:
                         migrationSucceeds' = res
                    /\ vms' = [vms EXCEPT ![vm[self]].mig_from = mig_from[self],
                                          ![vm[self]].state = "migrating"]
                    /\ pc' = [pc EXCEPT ![self] = "CreateVmm"]
                    /\ UNCHANGED << instance, vmReservations, v2p, 
                                    readInstance, readVmState, readDestVmState, 
                                    vm, mig_from >>

SetOpte(self) == /\ pc[self] = "SetOpte"
                 /\ v2p' = vm[self]
                 /\ pc' = [pc EXCEPT ![self] = "StartVmm"]
                 /\ UNCHANGED << instance, vms, vmReservations, 
                                 migrationSucceeds, readInstance, readVmState, 
                                 readDestVmState, vm, mig_from >>

StartVmm(self) == /\ pc[self] = "StartVmm"
                  /\ vms' = [vms EXCEPT ![vm[self]].state = "starting"]
                  /\ pc' = [pc EXCEPT ![self] = "CreateVmm"]
                  /\ UNCHANGED << instance, vmReservations, v2p, 
                                  migrationSucceeds, readInstance, readVmState, 
                                  readDestVmState, vm, mig_from >>

FailStart(self) == /\ pc[self] = "FailStart"
                   /\ instance' = [instance EXCEPT !.active = NULL,
                                                   !.gen = instance.gen + 1,
                                                   !.state = "stopped"]
                   /\ vms' = [vms EXCEPT ![vm[self]].state = "destroyed"]
                   /\ pc' = [pc EXCEPT ![self] = "CreateVmm"]
                   /\ UNCHANGED << vmReservations, v2p, migrationSucceeds, 
                                   readInstance, readVmState, readDestVmState, 
                                   vm, mig_from >>

starter(self) == CreateVmm(self) \/ MigrateVmm(self) \/ SetOpte(self)
                    \/ StartVmm(self) \/ FailStart(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in UPDATERS: updater(self))
           \/ (\E self \in VMS: vm_(self))
           \/ (\E self \in {STARTER}: starter(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in UPDATERS : WF_vars(updater(self))
        /\ \A self \in VMS : WF_vars(vm_(self))
        /\ \A self \in {STARTER} : WF_vars(starter(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
