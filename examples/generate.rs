//! # Generate _Mass Effect 2_ Outcome Data
//!
//! This example simply generates and serializes [`me2finale`] outcome data to a file using the
//! [MessagePack] format.
//!
//! ## Usage
//!
//! `cargo run --release --example generate -- PATH`
//!
//! - `PATH` is the path in which to store the outcome data. If a file already exists at the path,
//!   it will be replaced.
//!
//! > **NOTE:** The `--release` flag is crucial to minimize run time.
//!
//! [MessagePack]: https://msgpack.org/

use std::error::Error;
use std::fs::File;
use std::time::Instant;

use rmp_serde::Serializer;
use serde::Serialize;

fn main() -> Result<(), Box<dyn Error>> {
    let Some(path) = std::env::args().nth(1) else {
        return Err("PATH argument is required".into());
    };

    let file = File::create(&path)?;

    println!("Generating outcome data...");
    let generation_start = Instant::now();
    let outcome_map = me2finale::generate::outcome_map();
    let generation_seconds = generation_start.elapsed().as_secs_f32();
    println!("Generated all outcomes in {generation_seconds}s.");

    println!("Saving outcome data to {path}...");
    let mut serializer = Serializer::new(file);
    outcome_map.serialize(&mut serializer)?;
    println!("Done!");

    Ok(())
}
