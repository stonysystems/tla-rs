//! PrimaryBackup protocol service entry point.

use crate::common::framework::args_t::*;
use crate::common::framework::generic_main::*;
use crate::common::native::io_s::*;
use crate::implementation::PrimaryBackup::host::PrimaryBackupHost;

pub fn primarybackup_main(netc: NetClient, args: Args) -> Result<(), ProtocolError> {
    protocol_main::<PrimaryBackupHost>(netc, args)
}
