use crate::expr::{self, ColumnKind, Expr, PlonkVar as Var};
use num_bigint::BigUint;
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
    num_rows: usize,
    columns: Vec<ColumnWitness>,
    // The advice cells in the circuit, arranged as [column][row].
    witness: Vec<Vec<Option<BigUint>>>,
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
    fn new(name: String, phase: usize) -> Self {
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
    fn new(name: String) -> Self {
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
    fn new(name: String) -> Self {
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
    pub witness: Vec<ColumnWitness>,
    pub fixed: Vec<ColumnFixed>,
    pub public: Vec<ColumnPublic>,
}

#[derive(Debug, Clone)]
pub struct Poly {
    pub name: String,
    pub exp: Expr<Var>,
}

#[derive(Debug, Clone)]
pub struct Lookup {
    pub name: String,
    pub exps: (Vec<Expr<Var>>, Vec<Expr<Var>>),
}

#[derive(Debug, Clone)]
pub struct CopyC {
    pub columns: (expr::Column, expr::Column),
    pub offsets: Vec<(usize, usize)>,
}

#[derive(Debug, Default, Clone)]
pub struct Info {
    pub num_rows: usize,
    pub challenges: Vec<Challenge>,
}

/// Plonkish Arithmetization Format
#[derive(Debug, Default, Clone)]
pub struct Plaf {
    pub info: Info,
    pub columns: Columns,
    pub polys: Vec<Poly>,
    pub lookups: Vec<Lookup>,
    pub copys: Vec<CopyC>,
    pub fixed: Vec<Vec<Option<BigUint>>>,
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
