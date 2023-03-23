use crate::expr::{self, Column, ColumnKind, Expr, PlonkVar as Var};
use num_bigint::BigUint;
use num_traits::Zero;
use std::fmt::{self, Debug, Display, Write};

pub mod backends;
pub mod frontends;

/// The value of a particular cell within the circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CellValue<F> {
    // An unassigned cell.
    Unassigned,
    // A cell that has been assigned a value.
    Assigned(F),
    // A unique poisoned cell.
    // Poison(usize),
}

#[derive(Debug)]
pub struct Witness {
    pub num_rows: usize,
    pub columns: Vec<ColumnWitness>,
    // The advice cells in the circuit, arranged as [column][row].
    pub witness: Vec<Vec<Option<BigUint>>>,
}

/// Adaptor struct to format the witness columns assignments as CSV
pub struct WitnessDisplayCSV<'a>(pub &'a Witness);

impl Display for WitnessDisplayCSV<'_> {
    /// Format witness assignment as CSV
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let this = self.0;
        write!(f, "offset")?;
        for col in this.columns.iter() {
            write!(f, ",")?;
            write!(f, "{}", col.name())?;
        }
        writeln!(f)?;
        for row_idx in 0..this.num_rows {
            write!(f, "{}", row_idx)?;
            for col_idx in 0..this.columns.len() {
                write!(f, ",")?;
                if let Some(ref v) = this.witness[col_idx][row_idx] {
                    write!(f, "{}", v)?;
                }
            }
            writeln!(f)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct ColumnWitness {
    pub name: String,
    pub aliases: Vec<String>,
    pub phase: usize,
}

impl ColumnWitness {
    pub fn new(name: String, phase: usize) -> Self {
        Self {
            name,
            aliases: Vec::new(),
            phase,
        }
    }
    fn name(&self) -> &String {
        self.aliases.get(0).unwrap_or(&self.name)
    }
}

#[derive(Debug, Clone)]
pub struct ColumnFixed {
    pub name: String,
    pub aliases: Vec<String>,
}

impl ColumnFixed {
    pub fn new(name: String) -> Self {
        Self {
            name,
            aliases: Vec::new(),
        }
    }
    fn name(&self) -> &String {
        self.aliases.get(0).unwrap_or(&self.name)
    }
}

#[derive(Debug, Clone)]
pub struct ColumnPublic {
    pub name: String,
    pub aliases: Vec<String>,
}

impl ColumnPublic {
    pub fn new(name: String) -> Self {
        Self {
            name,
            aliases: Vec::new(),
        }
    }
    fn name(&self) -> &String {
        self.aliases.get(0).unwrap_or(&self.name)
    }
}

#[derive(Debug, Clone)]
pub struct Challenge {
    pub name: String,
    pub alias: Option<String>,
    pub phase: usize,
}

impl Challenge {
    fn new(name: String, phase: usize) -> Self {
        Self {
            name,
            alias: None,
            phase,
        }
    }
    fn name(&self) -> &String {
        self.alias.as_ref().unwrap_or(&self.name)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Columns {
    /// List of witness columns.  These are called "advice" in halo2.
    pub witness: Vec<ColumnWitness>,
    /// List of fixed columns.
    pub fixed: Vec<ColumnFixed>,
    /// List of public columns.  These are called "instance" in halo2.
    pub public: Vec<ColumnPublic>,
}

/// Polynomial constraint
#[derive(Debug, Clone)]
pub struct Poly {
    pub name: String,
    pub exp: Expr<Var>,
}

/// Lookup constraint
#[derive(Debug, Clone)]
pub struct Lookup {
    pub name: String,
    pub exps: (Vec<Expr<Var>>, Vec<Expr<Var>>),
}

/// Copy Constraint
#[derive(Debug, Clone)]
pub struct CopyC {
    pub columns: (expr::Column, expr::Column),
    pub offsets: Vec<(usize, usize)>,
}

/// Circuit general information
#[derive(Debug, Default, Clone)]
pub struct Info {
    /// Field modulus
    pub p: BigUint,
    /// Number of rows.  This is always a power of 2 in halo2.
    pub num_rows: usize,
    /// List of challenges used.  The challange API is a proving system extension applied to pse's
    /// fork of halo2: https://github.com/privacy-scaling-explorations/halo2/pull/97
    pub challenges: Vec<Challenge>,
}

/// Plonkish Arithmetization Format
#[derive(Debug, Default, Clone)]
pub struct Plaf {
    /// Circuit general information
    pub info: Info,
    /// Column information
    pub columns: Columns,
    /// List of polynomial identity constraints
    pub polys: Vec<Poly>,
    /// List of lookup constraints
    pub lookups: Vec<Lookup>,
    /// List of copy constraints
    pub copys: Vec<CopyC>,
    /// Assignment values to the fixed columns.  None is used for non-assigned values, which means
    /// a 0 value.
    pub fixed: Vec<Vec<Option<BigUint>>>,
}

pub struct VarDisplay<'a> {
    pub v: &'a Var,
    pub plaf: &'a Plaf,
}

impl Display for VarDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Var::*;
        match self.v {
            ColumnQuery { column, rotation } => {
                self.plaf.fmt_column(f, column)?;
                if *rotation != 0 {
                    write!(f, "[{}]", rotation)?;
                }
            }
            Challenge { index, phase: _ } => {
                write!(f, "{}", self.plaf.info.challenges[*index].name())?
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Cell {
    pub column: Column,
    pub offset: usize,
}

impl expr::Var for Cell {}

impl Display for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct CellDisplay<'a> {
    pub c: &'a Cell,
    pub plaf: &'a Plaf,
}

impl Display for CellDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.plaf.fmt_column(f, &self.c.column)?;
        write!(f, "[{}]", self.c.offset)?;
        Ok(())
    }
}

impl Plaf {
    pub fn fmt_column<W: Write>(&self, f: &mut W, c: &expr::Column) -> fmt::Result {
        use ColumnKind::*;
        write!(
            f,
            "{}",
            match c.kind {
                Witness => self.columns.witness[c.index].name(),
                Public => self.columns.public[c.index].name(),
                Fixed => self.columns.fixed[c.index].name(),
            }
        )
    }
    pub fn fmt_var<W: Write>(&self, f: &mut W, v: &Var) -> fmt::Result {
        match v {
            Var::ColumnQuery { column, rotation } => {
                self.fmt_column(f, column)?;
                if *rotation != 0 {
                    write!(f, "[{}]", rotation)?;
                }
                Ok(())
            }
            Var::Challenge { index, phase: _ } => {
                write!(f, "{}", self.info.challenges[*index].name())
            }
        }
    }
    pub fn set_challange_alias(&mut self, index: usize, name: String) -> bool {
        if let Some(mut challange) = self.info.challenges.get_mut(index) {
            challange.alias = Some(name);
            true
        } else {
            false
        }
    }

    pub fn resolve(&self, e: &Expr<Var>, offset: usize) -> Expr<Cell> {
        use Expr::*;
        match e {
            Neg(e) => Neg(Box::new(self.resolve(e, offset))),
            Const(f) => Const(f.clone()),
            Var(v) => match v {
                expr::PlonkVar::ColumnQuery { column, rotation } => {
                    let offset =
                        (offset as i32 + rotation).rem_euclid(self.info.num_rows as i32) as usize;
                    match column.kind {
                        ColumnKind::Fixed => Const(
                            self.fixed[column.index][offset]
                                .clone()
                                .unwrap_or_else(BigUint::zero),
                        ),
                        _ => Var(Cell {
                            column: *column,
                            offset,
                        }),
                    }
                }
                expr::PlonkVar::Challenge { index: _, phase: _ } => {
                    // TODO: Figure out something better :P
                    Const(BigUint::from(1234u64))
                }
            },
            Sum(es) => Sum(es.iter().map(|e| self.resolve(e, offset)).collect()),
            Mul(es) => Mul(es.iter().map(|e| self.resolve(e, offset)).collect()),
            Pow(e, f) => Pow(Box::new(self.resolve(e, offset)), *f),
        }
    }

    /// Simplify expressions in polynomial constraints and lookups.
    pub fn simplify(&mut self) {
        let p = &self.info.p;
        // Polynomial Expressions
        for poly in self.polys.iter_mut() {
            poly.exp.simplify(p);
        }
        // Lookups
        for lookup in self.lookups.iter_mut() {
            for (lhs, rhs) in lookup.exps.0.iter_mut().zip(lookup.exps.1.iter_mut()) {
                lhs.simplify(p);
                rhs.simplify(p);
            }
        }
    }
}

/// Adaptor struct to format the fixed columns assignments as CSV
pub struct PlafDisplayFixedCSV<'a>(pub &'a Plaf);

impl Display for PlafDisplayFixedCSV<'_> {
    /// Format fixed columns assignments as CSV
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let this = self.0;
        write!(f, "offset")?;
        for col in this.columns.fixed.iter() {
            write!(f, ",")?;
            write!(f, "{}", col.name())?;
        }
        writeln!(f)?;
        for row_idx in 0..this.info.num_rows {
            write!(f, "{}", row_idx)?;
            for col_idx in 0..this.columns.fixed.len() {
                write!(f, ",")?;
                if let Some(ref v) = this.fixed[col_idx][row_idx] {
                    write!(f, "{}", v)?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

/// Adaptor struct to format the entire Plaf as toml except for the Fixed Column assignments
pub struct PlafDisplayBaseTOML<'a>(pub &'a Plaf);

impl Display for PlafDisplayBaseTOML<'_> {
    /// Format entire Plaf as toml except for Fixed Columns assignments
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let this = self.0;
        writeln!(f, "[info]")?;
        writeln!(f, "num_rows = {}", this.info.num_rows)?;
        writeln!(f)?;

        writeln!(f, "[info.challenges]")?;
        for ch in &this.info.challenges {
            write!(f, "{} = {{ phase = {}", ch.name, ch.phase)?;
            if let Some(alias) = &ch.alias {
                writeln!(f, ", alias = \"{}\" }}", alias)?;
            } else {
                writeln!(f, "}}")?;
            }
        }
        writeln!(f)?;

        writeln!(f, "[columns.public]")?;
        for c in &this.columns.public {
            writeln!(f, "{} = {{ aliases = {:?} }}", c.name, c.aliases)?;
        }
        writeln!(f)?;

        writeln!(f, "[columns.fixed]")?;
        for c in &this.columns.fixed {
            writeln!(f, "{} = {{ aliases = {:?} }}", c.name, c.aliases)?;
        }
        writeln!(f)?;

        writeln!(f, "[columns.witness]")?;
        for c in &this.columns.witness {
            writeln!(
                f,
                "{} = {{ phase = {}, aliases = {:?} }}",
                c.name, c.phase, c.aliases
            )?;
        }
        writeln!(f)?;

        for p in &this.polys {
            writeln!(f, "[constraints.polys.\"{}\"]", p.name)?;
            write!(f, "c = \"")?;
            p.exp
                .fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &Var| {
                    this.fmt_var(f, v)
                })?;
            writeln!(f, "\"")?;
        }
        writeln!(f)?;

        for l in &this.lookups {
            writeln!(f, "[constraints.lookups.\"{}\"]", l.name)?;
            writeln!(f, "l = [")?;
            for (lhs, rhs) in l.exps.0.iter().zip(l.exps.1.iter()) {
                write!(f, "  [\"")?;
                lhs.fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &Var| {
                    this.fmt_var(f, v)
                })?;
                writeln!(f, "\",")?;
                write!(f, "   \"")?;
                rhs.fmt_ascii(f, &mut |f: &mut fmt::Formatter<'_>, v: &Var| {
                    this.fmt_var(f, v)
                })?;
                writeln!(f, "\"],")?;
            }
            writeln!(f, "]")?;
        }
        writeln!(f)?;

        for c in &this.copys {
            writeln!(f, "[[constraints.copys]]")?;
            write!(f, "columns = [\"")?;
            this.fmt_column(f, &c.columns.0)?;
            write!(f, "\", \"")?;
            this.fmt_column(f, &c.columns.1)?;
            writeln!(f, "\"]")?;
            writeln!(f, "offsets = [")?;
            for (a, b) in &c.offsets {
                writeln!(f, " [{}, {}],", a, b)?;
            }
            writeln!(f, "]")?;
        }
        writeln!(f)?;

        Ok(())
    }
}
