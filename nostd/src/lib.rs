#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate core;

extern crate byteorder;
extern crate arrayvec;

pub mod io;
pub mod io_ext;
pub mod error;
