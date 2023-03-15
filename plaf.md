# plaf: Plonkish Arithmetization Format

**Disclaimer**: This is a work in process and some parts of the implementation may be incomplete.

Plaf is an attempt to create a standard format for plonkish circuits so that it can be reused in components that work with plonkish arithmetization.

Plaf supports the following "plonkish arithmetization" features:
- Listing of columns (or commitment polynomials) with names (aliases)
- Listing of polynomail expressions constraints that use the columns at any level of rotation
- Listing of lookup constraints as list of expression pairs
- Listing of copy constraints as list of column pairs with list of offset pairs
- Partial support for the Challange API: https://github.com/privacy-scaling-explorations/halo2/pull/97
- Fixed column values

## Serialization & Deserialization

Plaf is currently implemented as a Rust struct but it can also be serialized.

The current implementation supports the serialization of a Plaf circuit into 2 parts:
- A csv file with the fixed column values
- The rest of the circuit definition in a toml file

Currently the deserialization is not implemented

## Motivation and goals

The first motivation is to have a standard format that can be reused among various plonkish systems so that frontends and backend become independent and can be made interchangeable.  The definition of frontend and backend used here is this:
- frontend: module that generates the plonkish circuit (encoded as a Plaf circuit), and also is able to generate the witness values
- backend: module that has the following functionalities:
    - receive a Plaf circuit and generate the corresponding verifying and proving keys.
    - receive a Plaf circuit, a proving key and the witness values and generate a proof.
    - receive a Plaf circuit, a verifying key and a proof and verify it.

The current implemnentation supports the halo2 frontend (the halo2 Rust API) and the halo2 backend (the halo2 provig system implementation).  Using halo2 as backend requires a small change in halo2 because the original version only supports circuits defined at compile time.  The approach I've followed to support runtime circuit definitions is to add `&self` to `Circuit::configure`: https://github.com/ed255/halo2/commit/63e969673de83a410f21553fabec8f4b35bda1a5

A second goal is to have a standard format that supports pretty serialization to help reviewing/auditing circuits.

A third goal is to have a standard format which circuit analysis tools can target so that they can be reused for circuits targeting different proving systems.
