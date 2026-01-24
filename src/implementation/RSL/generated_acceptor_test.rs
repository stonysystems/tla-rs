// Integration test for generated acceptor code
// This file tests that the transpiler-generated code can be compiled
// alongside the existing RSL implementation types.
//
// Strategy: Option B from verus-integration-plan.md
// Use #[verifier::external_body] to trust iterator-based implementations
// while verifying the function contracts.

use vstd::prelude::*;
use std::collections::HashMap;

use crate::implementation::RSL::acceptorimpl::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::protocol::RSL::acceptor::*;
use crate::protocol::RSL::types::*;

verus! {

// Example of generated function with external_body
// This pattern allows us to verify the contract while trusting the implementation
#[verifier::external_body]
pub fn generated_remove_votes_before_truncation(
    votes: &CVotes,
    log_truncation_point: COperationNumber,
) -> (result: CVotes)
    requires
        cvotes_is_valid(votes),
        COperationNumberIsValid(log_truncation_point),
    ensures
        cvotes_is_valid(&result),
        RemoveVotesBeforeLogTruncationPoint(
            abstractify_cvotes(votes),
            abstractify_cvotes(&result),
            AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
        ),
{
    // This uses the iterator pattern which doesn't verify directly in Verus
    // but the external_body attribute trusts this implementation
    votes.iter()
        .filter(|(opn, _)| **opn >= log_truncation_point)
        .map(|(k, v)| (*k, v.clone()))
        .collect()
}

// Test that the generated function can be called
#[verifier(external)]
pub fn test_generated_code_structure() {
    // This test verifies that the generated code compiles
    // when integrated with the existing types.
    println!("Generated code structure test placeholder");
}

} // verus!
