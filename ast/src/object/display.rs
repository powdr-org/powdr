use std::fmt::{Display, Formatter, Result};

use crate::{asm_analysis::combine_flags, write_items_indented};

use super::{Link, LinkFrom, LinkTo, Location, MachineInstanceGraph, Object, Operation};

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.limbs.join("_"))
    }
}

impl Display for MachineInstanceGraph {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f, "// Utilities")?;
        for (module_path, statements) in &self.statements {
            writeln!(f, "mod {module_path} {{")?;
            write_items_indented(f, statements)?;
            writeln!(f, "}}")?;
        }
        for (location, object) in &self.objects {
            writeln!(f, "// Object {location}")?;
            writeln!(f, "{object}")?;
            writeln!(f)?;
        }
        Ok(())
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f, "// Degree {}", self.degree)?;
        if !self.operations.is_empty() {
            writeln!(f, "// Operations:")?;
            for (name, operation) in &self.operations {
                writeln!(f, "// {name}: {operation}")?;
            }
        }
        writeln!(f, "// PIL:")?;
        for s in &self.pil {
            writeln!(f, "{s}")?;
        }
        if !self.links.is_empty() {
            writeln!(f, "// Links:")?;
            for link in &self.links {
                writeln!(f, "// {link}")?;
            }
        }
        Ok(())
    }
}

impl Display for Link {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} links to {}", self.from, self.to)
    }
}

impl Display for LinkFrom {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let flag = combine_flags(self.instr_flag.clone(), self.link_flag.clone());
        write!(f, "{flag} {}", self.params)
    }
}

impl Display for LinkTo {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} in {}", self.operation, self.machine)
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "operation with id {:?} with params {}",
            self.id.as_ref().map(|id| id.to_string()),
            self.params,
        )
    }
}
