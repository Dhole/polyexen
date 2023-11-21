#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate static_assertions;

pub mod analyze;
pub mod expr;
pub mod parser;
pub mod plaf;

#[cfg(all(feature = "halo2-pse", feature = "halo2-axiom"))]
compile_error!(
    "Cannot have both \"halo2-pse\" and \"halo2-axiom\" features enabled at the same time!"
);
#[cfg(not(any(feature = "halo2-pse", feature = "halo2-axiom")))]
compile_error!("Must enable exactly one of \"halo2-pse\" or \"halo2-axiom\" features to choose which halo2_proofs crate to use.");
#[cfg(feature = "halo2-axiom")]
pub use halo2_axiom as halo2_proofs;
#[cfg(feature = "halo2-pse")]
pub use halo2_proofs;
