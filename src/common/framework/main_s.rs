#![allow(unused_imports)]
use super::distributedsystem_s::*;
use super::environment_s::*;
use super::host_s::*;
use crate::common::logic::*;
use crate::common::native::io_s::*;
use vstd::prelude::*;
use vstd::{modes::*, prelude::*, seq::*, *};

// IronFleetMain trait was removed — the main loop is now implemented
// directly in each protocol's host module (host_i.rs / host.rs).
