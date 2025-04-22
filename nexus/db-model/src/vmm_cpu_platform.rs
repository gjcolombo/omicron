// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::InstanceMinimumCpuPlatform;

use super::impl_enum_type;
use serde::{Deserialize, Serialize};

impl_enum_type!(
    VmmCpuPlatformEnum:

    #[derive(
        Copy,
        Clone,
        Debug,
        PartialEq,
        AsExpression,
        FromSqlRow,
        Serialize,
        Deserialize,
        strum::Display
    )]
    pub enum VmmCpuPlatform;

    SledDefault => b"sled_default"
    AmdMilan => b"amd_milan"
);

impl From<InstanceMinimumCpuPlatform> for VmmCpuPlatform {
    fn from(value: InstanceMinimumCpuPlatform) -> Self {
        match value {
            InstanceMinimumCpuPlatform::AmdMilan => Self::AmdMilan,
        }
    }
}
