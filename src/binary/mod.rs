// Copyright Amazon.com, Inc. or its affiliates.

//! This module provides the necessary structures and logic to read values from a binary Ion
//! data stream.

// Public as a workaround for: https://github.com/amazon-ion/ion-rust/issues/484
pub mod constants;
pub mod decimal;
pub mod int;
pub mod timestamp;
pub(crate) mod type_code;
pub mod uint;
pub mod var_int;
pub mod var_uint;

pub use type_code::IonTypeCode;
