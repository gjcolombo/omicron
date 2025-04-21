// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use super::impl_enum_type;
use serde::{Deserialize, Serialize};

impl_enum_type!(
    InstanceMinimumCpuPlatformEnum:

    #[derive(
        Copy,
        Clone,
        Debug,
        PartialEq,
        AsExpression,
        FromSqlRow,
        Serialize,
        Deserialize
    )]
    pub enum InstanceMinimumCpuPlatform;

    AmdMilan=> b"amd_milan"
);

impl From<omicron_common::api::external::InstanceMinimumCpuPlatform>
    for InstanceMinimumCpuPlatform
{
    fn from(
        value: omicron_common::api::external::InstanceMinimumCpuPlatform,
    ) -> Self {
        use omicron_common::api::external::InstanceMinimumCpuPlatform as ApiPlatform;
        match value {
            ApiPlatform::AmdMilan => Self::AmdMilan,
        }
    }
}

impl From<InstanceMinimumCpuPlatform>
    for omicron_common::api::external::InstanceMinimumCpuPlatform
{
    fn from(value: InstanceMinimumCpuPlatform) -> Self {
        match value {
            InstanceMinimumCpuPlatform::AmdMilan => Self::AmdMilan,
        }
    }
}
