// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use super::impl_enum_type;
use serde::{Deserialize, Serialize};

impl_enum_type!(
    SledCpuFamilyEnum:

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
    pub enum SledCpuFamily;

    Unknown => b"unknown"
    AmdFamily19h => b"amd_family_19h"
    AmdFamily1Ah => b"amd_family_1ah"
);

impl From<nexus_types::internal_api::params::SledCpuFamily> for SledCpuFamily {
    fn from(value: nexus_types::internal_api::params::SledCpuFamily) -> Self {
        use nexus_types::internal_api::params::SledCpuFamily as InputFamily;
        match value {
            InputFamily::Unknown => Self::Unknown,
            InputFamily::AmdFamily19h => Self::AmdFamily19h,
            InputFamily::AmdFamily1Ah => Self::AmdFamily1Ah,
        }
    }
}

impl From<SledCpuFamily> for nexus_types::internal_api::params::SledCpuFamily {
    fn from(value: SledCpuFamily) -> Self {
        match value {
            SledCpuFamily::Unknown => Self::Unknown,
            SledCpuFamily::AmdFamily19h => Self::AmdFamily19h,
            SledCpuFamily::AmdFamily1Ah => Self::AmdFamily1Ah,
        }
    }
}
