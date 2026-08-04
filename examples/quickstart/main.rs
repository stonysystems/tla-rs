#![allow(non_snake_case)]

use vstd::prelude::*;

mod counter_gen;
mod counter_spec;

use counter_gen::{CIncrement, CInit};

fn main() {
    let zero = CInit();
    let one = CIncrement(&zero);
    println!("Counter: {} -> {}", zero, one);
}
