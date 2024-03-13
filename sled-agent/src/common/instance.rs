// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Describes the states of VM instances.

use crate::params::InstanceMigrationSourceParams;
use chrono::{DateTime, Utc};
use omicron_common::api::external::InstanceState as ApiInstanceState;
use omicron_common::api::internal::nexus::{
    InstanceRuntimeState, SledInstanceState, VmmRuntimeState,
};
use propolis_client::types::{
    InstanceMigrationStatus, InstanceState as PropolisApiState,
    InstanceStateMonitorResponse, MigrationState,
};
use uuid::Uuid;

/// The instance and VMM state that sled agent maintains on a per-VMM basis.
#[derive(Clone, Debug)]
pub struct InstanceStates {
    instance: InstanceRuntimeState,
    vmm: VmmRuntimeState,
    propolis_id: Uuid,
}

/// Newtype to allow conversion from Propolis API states (returned by the
/// Propolis state monitor) to Nexus VMM states.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PropolisInstanceState(PropolisApiState);

impl From<PropolisApiState> for PropolisInstanceState {
    fn from(value: PropolisApiState) -> Self {
        Self(value)
    }
}

impl From<PropolisInstanceState> for ApiInstanceState {
    fn from(value: PropolisInstanceState) -> Self {
        use propolis_client::types::InstanceState as State;
        match value.0 {
            // Nexus uses the VMM state as the externally-visible instance state
            // when an instance has an active VMM. A Propolis that is "creating"
            // its virtual machine objects is "starting" from the external API's
            // perspective.
            State::Creating | State::Starting => ApiInstanceState::Starting,
            State::Running => ApiInstanceState::Running,
            State::Stopping => ApiInstanceState::Stopping,
            // A Propolis that is stopped but not yet destroyed should still
            // appear to be Stopping from an external API perspective, since
            // they cannot be restarted yet. Instances become logically Stopped
            // once Propolis reports that the VM is Destroyed (see below).
            State::Stopped => ApiInstanceState::Stopping,
            State::Rebooting => ApiInstanceState::Rebooting,
            State::Migrating => ApiInstanceState::Migrating,
            State::Repairing => ApiInstanceState::Repairing,
            State::Failed => ApiInstanceState::Failed,
            // Nexus needs to learn when a VM has entered the "destroyed" state
            // so that it can release its resource reservation. When this
            // happens, this module also clears the active VMM ID from the
            // instance record, which will accordingly set the Nexus-owned
            // instance state to Stopped, preventing this state from being used
            // as an externally-visible instance state.
            State::Destroyed => ApiInstanceState::Destroyed,
        }
    }
}

/// Describes the status of the migration identified in an instance's runtime
/// state as it relates to any migration status information reported by the
/// instance's Propolis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObservedMigrationStatus {
    /// Propolis reported that migration isn't done yet.
    InProgress,

    /// Propolis reported that the migration completed successfully.
    Succeeded,

    /// Propolis reported that the migration failed.
    Failed,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ObservedMigration {
    id: Uuid,
    status: ObservedMigrationStatus,
}

impl From<InstanceMigrationStatus> for ObservedMigration {
    fn from(value: InstanceMigrationStatus) -> Self {
        ObservedMigration {
            id: value.id,
            status: match value.state {
                MigrationState::Finish => ObservedMigrationStatus::Succeeded,
                MigrationState::Error => ObservedMigrationStatus::Failed,
                _ => ObservedMigrationStatus::InProgress,
            },
        }
    }
}

/// The information observed by the instance's Propolis state monitor.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ObservedPropolisState {
    /// The state reported by Propolis's instance state monitor API.
    pub vmm_state: PropolisInstanceState,

    /// The status of the inbound migration into this Propolis, if there is or
    /// was such a migration.
    pub migration_in: Option<ObservedMigration>,

    /// The status of the most recent outbound migration from this Propolis, if
    /// there is or was such a migration.
    pub migration_out: Option<ObservedMigration>,

    /// The approximate time at which this observation was made.
    pub time: DateTime<Utc>,
}

impl From<InstanceStateMonitorResponse> for ObservedPropolisState {
    fn from(propolis_state: InstanceStateMonitorResponse) -> Self {
        Self {
            vmm_state: PropolisInstanceState(propolis_state.state),
            migration_in: propolis_state.migration.migration_in.map(Into::into),
            migration_out: propolis_state
                .migration
                .migration_out
                .map(Into::into),
            time: Utc::now(),
        }
    }
}

/// The set of instance states that sled agent can publish to Nexus. This is
/// a subset of the instance states Nexus knows about: the Creating and
/// Destroyed states are reserved for Nexus to use for instances that are being
/// created for the very first time or have been explicitly deleted.
pub enum PublishedVmmState {
    Stopping,
    Rebooting,
}

impl From<PublishedVmmState> for ApiInstanceState {
    fn from(value: PublishedVmmState) -> Self {
        match value {
            PublishedVmmState::Stopping => ApiInstanceState::Stopping,
            PublishedVmmState::Rebooting => ApiInstanceState::Rebooting,
        }
    }
}

/// The possible roles a VMM can have vis-a-vis an instance.
#[derive(Clone, Copy, Debug, PartialEq)]
enum PropolisRole {
    /// The VMM is its instance's current active VMM.
    Active,

    /// The VMM is its instance's migration target VMM.
    MigrationTarget,

    /// The instance does not refer to this VMM (but it may have done so in the
    /// past).
    Retired,
}

/// Action to be taken on behalf of state transition.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Action {
    /// Terminate the VM and associated service.
    Destroy,
}

impl InstanceStates {
    pub fn new(
        instance: InstanceRuntimeState,
        vmm: VmmRuntimeState,
        propolis_id: Uuid,
    ) -> Self {
        InstanceStates { instance, vmm, propolis_id }
    }

    pub fn instance(&self) -> &InstanceRuntimeState {
        &self.instance
    }

    pub fn vmm(&self) -> &VmmRuntimeState {
        &self.vmm
    }

    pub fn propolis_id(&self) -> Uuid {
        self.propolis_id
    }

    /// Creates a `SledInstanceState` structure containing the entirety of this
    /// structure's runtime state. This requires cloning; for simple read access
    /// use the `instance` or `vmm` accessors instead.
    pub fn sled_instance_state(&self) -> SledInstanceState {
        SledInstanceState {
            instance_state: self.instance.clone(),
            vmm_state: self.vmm.clone(),
            propolis_id: self.propolis_id,
        }
    }

    /// Update the known state of an instance based on an observed state from
    /// Propolis.
    pub(crate) fn apply_propolis_observation(
        &mut self,
        observed: &ObservedPropolisState,
    ) -> Option<Action> {
        let vmm_gone = matches!(
            observed.vmm_state.0,
            PropolisApiState::Destroyed | PropolisApiState::Failed
        );

        // Apply this observation to the VMM record. It is safe to apply the
        // Destroyed state directly here because this routine ensures that if
        // this VMM is active, it will be retired and an appropriate
        // non-Destroyed state applied to the instance itself.
        self.vmm.state = observed.vmm_state.into();
        self.vmm.gen = self.vmm.gen.next();
        self.vmm.time_updated = observed.time;

        // Apply the observation to resolve the instance's active migration, if
        // it has one.
        self.resolve_migration(observed);

        // If this Propolis has exited, tear down its zone. If it was in the
        // active position, immediately retire any migration that might have
        // been pending and clear the active Propolis ID so that the instance
        // can start somewhere else.
        //
        // N.B. It is important to refetch the current Propolis role here,
        //      because it might have changed in the course of dealing with a
        //      completed migration. (In particular, if this VMM is gone because
        //      it was the source of a successful migration out, control has
        //      been transferred to the target, and what was once an active VMM
        //      is now retired.)
        if vmm_gone {
            if self.propolis_role() == PropolisRole::Active {
                self.clear_migration_ids(observed.time);
                self.retire_active_propolis(observed.time);
            }
            Some(Action::Destroy)
        } else {
            None
        }
    }

    /// If the current instance has an active migration, attempts to resolve it
    /// using the migration status in `observed`.
    fn resolve_migration(&mut self, observed: &ObservedPropolisState) {
        // If the instance doesn't believe there's a migration in progress,
        // ignore any observed migration status. Note that Propolis will
        // continue to report past migration statuses in its status updates even
        // after those migrations complete (to help ensure that sled agent won't
        // miss a migration status).
        let Some(expected_migration_id) = self.instance.migration_id else {
            return;
        };

        // The migration of interest depends on the role that this sled's VMM
        // plays in the instance's lifecycle: if it's the current active VMM,
        // look at the migration out; if it's a migration target, look at the
        // migration in.
        match self.propolis_role() {
            PropolisRole::Active => match observed.migration_out {
                // It's possible that Propolis isn't reporting a migration yet
                // (the destination may not have connected to the source yet).
                // This is fine; just fall through and update the VMM as normal.
                None => {}

                // If Propolis reported an outbound migration that doesn't match
                // what's in the instance record (either because there's no ID
                // in the record at all or there is one but it's different),
                // assume Propolis is reporting the status of a prior failed
                // migration out and fall through.
                Some(ObservedMigration { id, .. })
                    if id != expected_migration_id => {}

                // The IDs match, so interpret the migration status.
                Some(ObservedMigration { status, .. }) => match status {
                    // Migration is done: transfer responsibility to the
                    // target, but don't clear the active migration ID yet
                    // so that the instance will still appear to be
                    // migrating until the target acknowledges that it's
                    // able to migrate out.
                    ObservedMigrationStatus::Succeeded => {
                        self.switch_propolis_id_to_target(observed.time);

                        assert_eq!(self.propolis_role(), PropolisRole::Retired);
                    }

                    // Migration failed: just clear the IDs so the migration can
                    // be tried again.
                    ObservedMigrationStatus::Failed => {
                        self.clear_migration_ids(observed.time);
                    }

                    // Migration is still in progress: nothing to update yet.
                    ObservedMigrationStatus::InProgress => {}
                },
            },
            PropolisRole::MigrationTarget => match observed.migration_in {
                // This is unexpected: the agent should only start receiving
                // observations from the monitor thread after sending an
                // instance ensure request to Propolis, and sending a
                // migration-in ensure request should make all subsequent state
                // observations contain some migration status.
                //
                // Don't panic, though; just fall through so that the VMM gets
                // updated properly.
                None => {}

                // This is also unexpected: migration targets don't get reused
                // if a migration fails, so Propolis shouldn't be reporting the
                // state of a prior failed migration in. (It's also unexpected
                // that Propolis would report a migration ID while the instance
                // record has no such ID, since there must be a migration in the
                // record for this routine to have concluded that the current
                // Propolis is a migration target.)
                //
                // As before, don't panic the whole sled agent for this; just
                // fall through so that the VMM can be updated.
                Some(ObservedMigration { id, .. })
                    if id != expected_migration_id => {}

                // The IDs match, so interpret the migration status.
                Some(ObservedMigration { status, .. }) => {
                    match status {
                        // On a successful migration in, transfer control to the
                        // target *and* clear the migration ID to signal that a
                        // new migration can begin.
                        //
                        // Note that these calls increment the instance's
                        // generation number twice. This is by design and allows
                        // the target's migration-ID-clearing update to overtake
                        // the source's update.
                        ObservedMigrationStatus::Succeeded => {
                            self.switch_propolis_id_to_target(observed.time);
                            self.clear_migration_ids(observed.time);

                            assert_eq!(
                                self.propolis_role(),
                                PropolisRole::Active
                            );
                        }

                        // This is a failed migration in. Leave the migration
                        // IDs alone so that the migration won't appear to have
                        // concluded until the source is ready to start a new
                        // migration.
                        ObservedMigrationStatus::Failed => {}

                        // The migration's still in doubt, so don't move any IDs
                        // around yet.
                        ObservedMigrationStatus::InProgress => {}
                    }
                }
            },

            // This is a further update from a Propolis that's no longer part of
            // the instance; there's nothing else to tweak here.
            PropolisRole::Retired => {}
        }
    }

    /// Yields the role that this structure's VMM has given the structure's
    /// current instance state.
    fn propolis_role(&self) -> PropolisRole {
        if let Some(active_id) = self.instance.propolis_id {
            if active_id == self.propolis_id {
                return PropolisRole::Active;
            }
        }

        if let Some(dst_id) = self.instance.dst_propolis_id {
            if dst_id == self.propolis_id {
                return PropolisRole::MigrationTarget;
            }
        }

        PropolisRole::Retired
    }

    /// Sets the no-VMM fallback state of the current instance to reflect the
    /// state of its terminated VMM and clears the instance's current Propolis
    /// ID. Note that this routine does not touch any migration IDs.
    ///
    /// This should only be called by the state block for an active VMM and only
    /// when that VMM is in a terminal state (Destroyed or Failed).
    fn retire_active_propolis(&mut self, now: DateTime<Utc>) {
        assert!(self.propolis_role() == PropolisRole::Active);

        self.instance.propolis_id = None;
        self.instance.gen = self.instance.gen.next();
        self.instance.time_updated = now;
    }

    /// Moves the instance's destination Propolis ID into the current active
    /// position and updates the generation number, but does not clear the
    /// destination ID or the active migration ID. This promotes a migration
    /// target VMM into the active position without actually allowing a new
    /// migration to begin.
    ///
    /// This routine should only be called when
    /// `instance.dst_propolis_id.is_some()`.
    fn switch_propolis_id_to_target(&mut self, now: DateTime<Utc>) {
        assert!(self.instance.dst_propolis_id.is_some());

        self.instance.propolis_id = self.instance.dst_propolis_id;
        self.instance.gen = self.instance.gen.next();
        self.instance.time_updated = now;
    }

    /// Forcibly transitions this instance's VMM into the specified `next`
    /// state and updates its generation number.
    pub(crate) fn transition_vmm(
        &mut self,
        next: PublishedVmmState,
        now: DateTime<Utc>,
    ) {
        self.vmm.state = next.into();
        self.vmm.gen = self.vmm.gen.next();
        self.vmm.time_updated = now;
    }

    /// Updates the state of this instance in response to a rude termination of
    /// its Propolis zone, marking the VMM as destroyed and applying any
    /// consequent state updates.
    ///
    /// # Synchronization
    ///
    /// A caller who is rudely terminating a Propolis zone must hold locks
    /// sufficient to ensure that no other Propolis observations arrive in the
    /// transaction that terminates the zone and then calls this function.
    ///
    /// TODO(#4004): This routine works by synthesizing a Propolis state change
    /// that says "this Propolis is destroyed and its active migrations failed."
    /// If this conflicts with the actual Propolis state--e.g., if the
    /// underlying Propolis was destroyed but migration *succeeded*--the
    /// instance's state in Nexus may become inconsistent. This routine should
    /// therefore only be invoked by callers who know that an instance is not
    /// migrating.
    pub(crate) fn terminate_rudely(&mut self) {
        let fake_observed = ObservedPropolisState {
            vmm_state: PropolisInstanceState(PropolisApiState::Destroyed),
            migration_in: self.instance.migration_id.map(|id| {
                ObservedMigration {
                    id,
                    status: ObservedMigrationStatus::Failed,
                }
            }),
            migration_out: self.instance.migration_id.map(|id| {
                ObservedMigration {
                    id,
                    status: ObservedMigrationStatus::Failed,
                }
            }),
            time: Utc::now(),
        };

        self.apply_propolis_observation(&fake_observed);
    }

    /// Sets or clears this instance's migration IDs and advances its Propolis
    /// generation number.
    pub(crate) fn set_migration_ids(
        &mut self,
        ids: &Option<InstanceMigrationSourceParams>,
        now: DateTime<Utc>,
    ) {
        if let Some(ids) = ids {
            self.instance.migration_id = Some(ids.migration_id);
            self.instance.dst_propolis_id = Some(ids.dst_propolis_id);
        } else {
            self.instance.migration_id = None;
            self.instance.dst_propolis_id = None;
        }

        self.instance.gen = self.instance.gen.next();
        self.instance.time_updated = now;
    }

    /// Unconditionally clears the instance's migration IDs and advances its
    /// Propolis generation. Not public; used internally to conclude migrations.
    fn clear_migration_ids(&mut self, now: DateTime<Utc>) {
        self.instance.migration_id = None;
        self.instance.dst_propolis_id = None;
        self.instance.gen = self.instance.gen.next();
        self.instance.time_updated = now;
    }

    /// Returns true if the migration IDs in this instance are already set as they
    /// would be on a successful transition from the migration IDs in
    /// `old_runtime` to the ones in `migration_ids`.
    pub(crate) fn migration_ids_already_set(
        &self,
        old_runtime: &InstanceRuntimeState,
        migration_ids: &Option<InstanceMigrationSourceParams>,
    ) -> bool {
        // For the old and new records to match, the new record's Propolis
        // generation must immediately succeed the old record's.
        //
        // This is an equality check to try to avoid the following A-B-A
        // problem:
        //
        // 1. Instance starts on sled 1.
        // 2. Parallel sagas start, one to migrate the instance to sled 2
        //    and one to migrate the instance to sled 3.
        // 3. The "migrate to sled 2" saga completes.
        // 4. A new migration starts that migrates the instance back to sled 1.
        // 5. The "migrate to sled 3" saga attempts to set its migration
        //    ID.
        //
        // A simple less-than check allows the migration to sled 3 to proceed
        // even though the most-recently-expressed intent to migrate put the
        // instance on sled 1.
        if old_runtime.gen.next() != self.instance.gen {
            return false;
        }

        match (self.instance.migration_id, migration_ids) {
            // If the migration ID is already set, and this is a request to set
            // IDs, the records match if the relevant IDs match.
            (Some(current_migration_id), Some(ids)) => {
                let current_dst_id = self.instance.dst_propolis_id.expect(
                    "migration ID and destination ID must be set together",
                );

                current_migration_id == ids.migration_id
                    && current_dst_id == ids.dst_propolis_id
            }
            // If the migration ID is already cleared, and this is a request to
            // clear IDs, the records match.
            (None, None) => {
                assert!(self.instance.dst_propolis_id.is_none());
                true
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::params::InstanceMigrationSourceParams;

    use chrono::Utc;
    use omicron_common::api::external::Generation;
    use omicron_common::api::internal::nexus::InstanceRuntimeState;
    use propolis_client::types::InstanceState as Observed;
    use uuid::Uuid;

    fn make_instance() -> InstanceStates {
        let propolis_id = Uuid::new_v4();
        let now = Utc::now();
        let instance = InstanceRuntimeState {
            propolis_id: Some(propolis_id),
            dst_propolis_id: None,
            migration_id: None,
            gen: Generation::new(),
            time_updated: now,
        };

        let vmm = VmmRuntimeState {
            state: ApiInstanceState::Starting,
            gen: Generation::new(),
            time_updated: now,
        };

        InstanceStates::new(instance, vmm, propolis_id)
    }

    fn make_migration_source_instance() -> InstanceStates {
        let mut state = make_instance();
        state.vmm.state = ApiInstanceState::Migrating;
        state.instance.migration_id = Some(Uuid::new_v4());
        state.instance.dst_propolis_id = Some(Uuid::new_v4());
        state
    }

    fn make_migration_target_instance() -> InstanceStates {
        let mut state = make_instance();
        state.vmm.state = ApiInstanceState::Migrating;
        state.instance.migration_id = Some(Uuid::new_v4());
        state.propolis_id = Uuid::new_v4();
        state.instance.dst_propolis_id = Some(state.propolis_id);
        state
    }

    fn make_observed_state(
        propolis_state: PropolisInstanceState,
    ) -> ObservedPropolisState {
        ObservedPropolisState {
            vmm_state: propolis_state,
            migration_in: None,
            migration_out: None,
            time: Utc::now(),
        }
    }

    /// Checks to see if the instance state structures `prev` and `next` have a
    /// difference that should produce a change in generation and asserts that
    /// such a change occurred.
    fn assert_state_change_has_gen_change(
        prev: &InstanceStates,
        next: &InstanceStates,
    ) {
        // The predicate under test below is "if an interesting field changed,
        // then the generation number changed." Testing the contrapositive is a
        // little nicer because the assertion that trips identifies exactly
        // which field changed without updating the generation number.
        //
        // The else branch tests the converse to make sure the generation number
        // does not update unexpectedly. While this won't cause an important
        // state update to be dropped, it can interfere with updates from other
        // sleds that expect their own attempts to advance the generation number
        // to cause new state to be recorded.
        if prev.instance.gen == next.instance.gen {
            assert_eq!(prev.instance.propolis_id, next.instance.propolis_id);
            assert_eq!(
                prev.instance.dst_propolis_id,
                next.instance.dst_propolis_id
            );
            assert_eq!(prev.instance.migration_id, next.instance.migration_id);
        } else {
            assert!(
                (prev.instance.propolis_id != next.instance.propolis_id)
                    || (prev.instance.dst_propolis_id
                        != next.instance.dst_propolis_id)
                    || (prev.instance.migration_id
                        != next.instance.migration_id),
                "prev: {:?}, next: {:?}",
                prev,
                next
            );
        }

        // Propolis is free to publish no-op VMM state updates (e.g. when an
        // in-progress migration's state changes but the migration is not yet
        // complete), so don't test the converse here.
        if prev.vmm.gen == next.vmm.gen {
            assert_eq!(prev.vmm.state, next.vmm.state);
        }
    }

    #[test]
    fn propolis_terminal_states_request_destroy_action() {
        for state in [Observed::Destroyed, Observed::Failed] {
            let mut instance_state = make_instance();
            let original_instance_state = instance_state.clone();
            let requested_action = instance_state
                .apply_propolis_observation(&make_observed_state(state.into()));

            assert!(matches!(requested_action, Some(Action::Destroy)));
            assert!(
                instance_state.instance.gen
                    > original_instance_state.instance.gen
            );
        }
    }

    #[test]
    fn destruction_after_migration_out_does_not_transition() {
        let mut state = make_migration_source_instance();
        assert!(state.instance.dst_propolis_id.is_some());
        assert_ne!(state.instance.propolis_id, state.instance.dst_propolis_id);

        // After a migration succeeds, the source VM appears to stop but reports
        // that the migration has succeeded.
        let mut observed = ObservedPropolisState {
            vmm_state: PropolisInstanceState(Observed::Stopping),
            migration_in: None,
            migration_out: Some(ObservedMigration {
                id: state.instance.migration_id.unwrap(),
                status: ObservedMigrationStatus::Succeeded,
            }),
            time: Utc::now(),
        };

        // This transition should transfer control to the target VMM without
        // actually marking the migration as completed. This advances the
        // instance's state generation.
        let prev = state.clone();
        assert!(state.apply_propolis_observation(&observed).is_none());
        assert_state_change_has_gen_change(&prev, &state);
        assert!(state.instance.gen > prev.instance.gen);
        assert_eq!(
            state.instance.dst_propolis_id,
            prev.instance.dst_propolis_id
        );
        assert_eq!(state.instance.propolis_id, state.instance.dst_propolis_id);
        assert!(state.instance.migration_id.is_some());

        // Once a successful migration is observed, the VMM's state should
        // continue to update, but the instance's state shouldn't change
        // anymore.
        let prev = state.clone();
        observed.vmm_state = PropolisInstanceState(Observed::Stopped);
        assert!(state.apply_propolis_observation(&observed).is_none());
        assert_state_change_has_gen_change(&prev, &state);
        assert_eq!(state.instance.gen, prev.instance.gen);

        // The Stopped state is translated internally to Stopping to prevent
        // external viewers from perceiving that the instance is stopped before
        // the VMM is fully retired.
        assert_eq!(state.vmm.state, ApiInstanceState::Stopping);
        assert!(state.vmm.gen > prev.vmm.gen);

        let prev = state.clone();
        observed.vmm_state = PropolisInstanceState(Observed::Destroyed);
        assert!(matches!(
            state.apply_propolis_observation(&observed),
            Some(Action::Destroy)
        ));
        assert_state_change_has_gen_change(&prev, &state);
        assert_eq!(state.instance.gen, prev.instance.gen);
        assert_eq!(state.vmm.state, ApiInstanceState::Destroyed);
        assert!(state.vmm.gen > prev.vmm.gen);
    }

    #[test]
    fn failure_after_migration_in_does_not_transition() {
        let mut state = make_migration_target_instance();

        // Failure to migrate into an instance should mark the VMM as destroyed
        // but should not change the instance's migration IDs.
        let observed = ObservedPropolisState {
            vmm_state: PropolisInstanceState(Observed::Failed),
            migration_in: Some(ObservedMigration {
                id: state.instance.migration_id.unwrap(),
                status: ObservedMigrationStatus::Failed,
            }),
            migration_out: None,
            time: Utc::now(),
        };

        let prev = state.clone();
        assert!(matches!(
            state.apply_propolis_observation(&observed),
            Some(Action::Destroy)
        ));
        assert_state_change_has_gen_change(&prev, &state);
        assert_eq!(state.instance.gen, prev.instance.gen);
        assert_eq!(state.vmm.state, ApiInstanceState::Failed);
        assert!(state.vmm.gen > prev.vmm.gen);
    }

    // Verifies that the rude-termination state change doesn't update the
    // instance record if the VMM under consideration is a migration target.
    //
    // The live migration saga relies on this property for correctness (it needs
    // to know that unwinding its "create destination VMM" step will not produce
    // an updated instance record).
    #[test]
    fn rude_terminate_of_migration_target_does_not_transition_instance() {
        let mut state = make_migration_target_instance();
        assert_eq!(state.propolis_role(), PropolisRole::MigrationTarget);

        let prev = state.clone();
        state.terminate_rudely();

        assert_state_change_has_gen_change(&prev, &state);
        assert_eq!(state.instance.gen, prev.instance.gen);
    }

    #[test]
    fn migration_out_after_migration_in() {
        let mut state = make_migration_target_instance();
        let mut observed = ObservedPropolisState {
            vmm_state: PropolisInstanceState(Observed::Running),
            migration_in: Some(ObservedMigration {
                id: state.instance.migration_id.unwrap(),
                status: ObservedMigrationStatus::Succeeded,
            }),
            migration_out: None,
            time: Utc::now(),
        };

        // The transition into the Running state on the migration target should
        // take over for the source, updating the Propolis generation.
        let prev = state.clone();
        assert!(state.apply_propolis_observation(&observed).is_none());
        assert_state_change_has_gen_change(&prev, &state);
        assert!(state.instance.migration_id.is_none());
        assert!(state.instance.dst_propolis_id.is_none());
        assert!(state.instance.gen > prev.instance.gen);
        assert_eq!(state.vmm.state, ApiInstanceState::Running);
        assert!(state.vmm.gen > prev.vmm.gen);

        // Pretend Nexus set some new migration IDs.
        let prev = state.clone();
        let migration_id = Uuid::new_v4();
        state.set_migration_ids(
            &Some(InstanceMigrationSourceParams {
                migration_id,
                dst_propolis_id: Uuid::new_v4(),
            }),
            Utc::now(),
        );
        assert_state_change_has_gen_change(&prev, &state);
        assert!(state.instance.gen > prev.instance.gen);
        assert_eq!(state.vmm.gen, prev.vmm.gen);

        // Mark that the new migration out is in progress. This doesn't change
        // anything in the instance runtime state, but does update the VMM state
        // generation.
        let prev = state.clone();
        observed.vmm_state = PropolisInstanceState(Observed::Migrating);
        observed.migration_out = Some(ObservedMigration {
            id: migration_id,
            status: ObservedMigrationStatus::InProgress,
        });
        assert!(state.apply_propolis_observation(&observed).is_none());
        assert_state_change_has_gen_change(&prev, &state);
        assert_eq!(
            state.instance.migration_id.unwrap(),
            prev.instance.migration_id.unwrap()
        );
        assert_eq!(
            state.instance.dst_propolis_id.unwrap(),
            prev.instance.dst_propolis_id.unwrap()
        );
        assert_eq!(state.vmm.state, ApiInstanceState::Migrating);
        assert!(state.vmm.gen > prev.vmm.gen);
        assert_eq!(state.instance.gen, prev.instance.gen);

        // Propolis will publish that the migration succeeds before changing any
        // state. This should transfer control to the target but should not
        // touch the migration ID (that is the new target's job).
        let prev = state.clone();
        observed.vmm_state = PropolisInstanceState(Observed::Migrating);
        observed.migration_out = Some(ObservedMigration {
            id: migration_id,
            status: ObservedMigrationStatus::Succeeded,
        });
        assert!(state.apply_propolis_observation(&observed).is_none());
        assert_state_change_has_gen_change(&prev, &state);
        assert_eq!(state.vmm.state, ApiInstanceState::Migrating);
        assert!(state.vmm.gen > prev.vmm.gen);
        assert_eq!(state.instance.migration_id, prev.instance.migration_id);
        assert_eq!(
            state.instance.dst_propolis_id,
            prev.instance.dst_propolis_id,
        );
        assert_eq!(state.instance.propolis_id, state.instance.dst_propolis_id);
        assert!(state.instance.gen > prev.instance.gen);

        // The rest of the destruction sequence is covered by other tests.
    }

    #[test]
    fn test_migration_ids_already_set() {
        let orig_instance = make_instance();
        let mut old_instance = orig_instance.clone();
        let mut new_instance = old_instance.clone();

        // Advancing the old instance's migration IDs and then asking if the
        // new IDs are present should indicate that they are indeed present.
        let migration_ids = InstanceMigrationSourceParams {
            migration_id: Uuid::new_v4(),
            dst_propolis_id: Uuid::new_v4(),
        };

        new_instance.set_migration_ids(&Some(migration_ids), Utc::now());
        assert!(new_instance.migration_ids_already_set(
            old_instance.instance(),
            &Some(migration_ids)
        ));

        // The IDs aren't already set if the new record has an ID that's
        // advanced from the old record by more than one generation.
        let mut newer_instance = new_instance.clone();
        newer_instance.instance.gen = newer_instance.instance.gen.next();
        assert!(!newer_instance.migration_ids_already_set(
            old_instance.instance(),
            &Some(migration_ids)
        ));

        // They also aren't set if the old generation has somehow equaled or
        // surpassed the current generation.
        old_instance.instance.gen = old_instance.instance.gen.next();
        assert!(!new_instance.migration_ids_already_set(
            old_instance.instance(),
            &Some(migration_ids)
        ));

        // If the generation numbers are right, but either requested ID is not
        // present in the current instance, the requested IDs aren't set.
        old_instance = orig_instance;
        new_instance.instance.migration_id = Some(Uuid::new_v4());
        assert!(!new_instance.migration_ids_already_set(
            old_instance.instance(),
            &Some(migration_ids)
        ));

        new_instance.instance.migration_id = Some(migration_ids.migration_id);
        new_instance.instance.dst_propolis_id = Some(Uuid::new_v4());
        assert!(!new_instance.migration_ids_already_set(
            old_instance.instance(),
            &Some(migration_ids)
        ));

        new_instance.instance.migration_id = None;
        new_instance.instance.dst_propolis_id = None;
        assert!(!new_instance.migration_ids_already_set(
            old_instance.instance(),
            &Some(migration_ids)
        ));
    }
}
