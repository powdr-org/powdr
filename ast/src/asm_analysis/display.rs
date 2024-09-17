use std::{
    fmt::{Display, Formatter, Result},
    iter::once,
};

use itertools::Itertools;

use crate::{
    asm_analysis::combine_flags,
    indent,
    parsed::{
        asm::{AbsoluteSymbolPath, Part},
        display::format_type_scheme_around_name,
        TypedExpression,
    },
    write_indented_by, write_items_indented,
};

use super::{
    AnalysisASMFile, AssignmentStatement, CallableSymbol, CallableSymbolDefinitionRef,
    DebugDirective, FunctionBody, FunctionStatement, FunctionStatements, Incompatible,
    IncompatibleSet, InstructionDefinitionStatement, InstructionStatement, Item, LabelStatement,
    LinkDefinition, Machine, MachineDegree, RegisterDeclarationStatement, RegisterTy, Return, Rom,
    SubmachineDeclaration, TypeDeclaration,
};

impl Display for AnalysisASMFile {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut current_path = AbsoluteSymbolPath::default();

        for (path, item) in &self.items {
            let relative_path = path.relative_to(&current_path);
            let name = relative_path.name();
            // Skip the name (last) part
            for part in relative_path.parts().rev().skip(1).rev() {
                match part {
                    Part::Super => {
                        current_path.pop();
                        write_indented_by(f, "}\n", current_path.len())?;
                    }
                    Part::Named(m) => {
                        write_indented_by(f, format!("mod {m} {{\n"), current_path.len())?;
                        current_path.push(m.clone());
                    }
                }
            }

            match item {
                Item::Machine(machine) => {
                    write_indented_by(f, format!("machine {name}{machine}"), current_path.len())?;
                }
                Item::Expression(TypedExpression { e, type_scheme }) => write_indented_by(
                    f,
                    format!(
                        "let{} = {e};\n",
                        format_type_scheme_around_name(name, type_scheme)
                    ),
                    current_path.len(),
                )?,
                Item::TypeDeclaration(TypeDeclaration::Enum(enum_decl)) => {
                    write_indented_by(f, enum_decl, current_path.len())?
                }
                Item::TypeDeclaration(TypeDeclaration::Struct(struct_decl)) => {
                    write_indented_by(f, struct_decl, current_path.len())?
                }
                Item::TraitImplementation(trait_impl) => {
                    write_indented_by(f, trait_impl, current_path.len())?
                }
                Item::TraitDeclaration(trait_decl) => {
                    write_indented_by(f, trait_decl, current_path.len())?
                }
            }
        }
        for i in (0..current_path.len()).rev() {
            write_indented_by(f, "}\n", i)?;
        }

        Ok(())
    }
}

impl Display for MachineDegree {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match (&self.min, &self.max) {
            (Some(min), Some(max)) if min == max => write!(f, "degree: {min}"),
            (min, max) => write!(
                f,
                "{}",
                min.iter()
                    .map(|min_degree| format!("min_degree: {min_degree}"))
                    .chain(
                        max.iter()
                            .map(|max_degree| format!("max_degree: {max_degree}")),
                    )
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl Display for Machine {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let props = std::iter::once(&self.degree)
            .map(|d| format!("{d}"))
            .chain(self.latch.as_ref().map(|s| format!("latch: {s}")))
            .chain(
                self.operation_id
                    .as_ref()
                    .map(|s| format!("operation_id: {s}")),
            )
            .chain(
                self.call_selectors
                    .as_ref()
                    .map(|s| format!("call_selectors: {s}")),
            )
            .join(", ");
        if !props.is_empty() {
            write!(f, " with {props}")?;
        }

        writeln!(f, " {{")?;

        write_items_indented(f, &self.submachines)?;
        write_items_indented(f, &self.registers)?;
        write_items_indented(f, &self.instructions)?;
        write_items_indented(f, &self.callable)?;
        write_items_indented(f, &self.pil)?;
        write_items_indented(f, &self.links)?;

        writeln!(f, "}}")
    }
}

impl Display for LinkDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let flag = combine_flags(self.instr_flag.clone(), self.link_flag.clone());
        write!(
            f,
            "link {}{} {};",
            if flag == 1.into() {
                "".to_string()
            } else {
                format!("if {flag} ")
            },
            if self.is_permutation { "~>" } else { "=>" },
            self.to
        )
    }
}

impl Display for SubmachineDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} {}", self.ty, self.name)
    }
}

impl Display for Rom {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f, "rom {{")?;
        writeln!(f, "{}", indent(&self.statements, 1))?;
        write!(f, "}}")
    }
}

impl Display for FunctionStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FunctionStatement::Assignment(s) => write!(f, "{s}"),
            FunctionStatement::Instruction(s) => write!(f, "{s}"),
            FunctionStatement::Label(s) => write!(f, "{s}"),
            FunctionStatement::DebugDirective(d) => write!(f, "{d}"),
            FunctionStatement::Return(r) => write!(f, "{r}"),
        }
    }
}

impl Display for AssignmentStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{} <={}= {};",
            self.lhs().format(", "),
            self.assignment_registers().format(", "),
            self.rhs
        )
    }
}

impl Display for DebugDirective {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.directive)
    }
}

impl Display for InstructionStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "{}{};",
            self.instruction,
            if self.inputs.is_empty() {
                "".to_string()
            } else {
                format!(" {}", self.inputs.iter().format(", "))
            }
        )
    }
}

impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "return{};",
            if self.values.is_empty() {
                "".to_string()
            } else {
                format!(" {}", self.values.iter().format(", "))
            }
        )
    }
}

impl Display for LabelStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}:", self.name)
    }
}

impl Display for RegisterDeclarationStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "reg {}{};", self.name, self.ty,)
    }
}

impl Display for RegisterTy {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Assignment => write!(f, "[<=]"),
            Self::Write => write!(f, ""),
            Self::ReadOnly => write!(f, "[@r]"),
            Self::Pc => write!(f, "[@pc]"),
        }
    }
}

impl Display for InstructionDefinitionStatement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "instr {}{}", self.name, self.instruction)
    }
}

impl<'a> Display for CallableSymbolDefinitionRef<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match &self.symbol {
            CallableSymbol::Function(s) => {
                writeln!(
                    f,
                    "function {}{} {{",
                    self.name,
                    s.params.prepend_space_if_non_empty()
                )?;
                writeln!(f, "{}", indent(&s.body, 1))?;
                write!(f, "}}")
            }
            CallableSymbol::Operation(s) => {
                write!(
                    f,
                    "operation {}{}{};",
                    self.name,
                    s.id,
                    s.params.prepend_space_if_non_empty()
                )
            }
        }
    }
}

impl Display for FunctionStatements {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let res = match self.batches.is_some() {
            true => self
                .iter_batches()
                .flat_map(|batch| {
                    batch
                        .statements
                        .iter()
                        .map(|s| s.to_string())
                        .chain(once(format!(
                            "// END BATCH{}",
                            batch
                                .reason
                                .as_ref()
                                .map(|reason| format!(" {reason}"))
                                .unwrap_or_default()
                        )))
                })
                .join("\n"),
            false => self.iter().format("\n").to_string(),
        };
        write!(f, "{res}")
    }
}

impl Display for FunctionBody {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.statements)
    }
}

impl Display for Incompatible {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{self:?}")
    }
}

impl Display for IncompatibleSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.0.iter().format(", "))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parsed::asm::parse_absolute_path;
    use pretty_assertions::assert_eq;

    #[test]
    fn display_asm_analysis_file() {
        let file = AnalysisASMFile {
            items: [
                "::x::Y",
                "::x::r::T",
                "::x::f::Y",
                "::M",
                "::t::x::y::R",
                "::t::F",
                "::X",
            ]
            .into_iter()
            .map(|s| (parse_absolute_path(s), Item::Machine(Machine::default())))
            .collect(),
        };
        assert_eq!(
            file.to_string(),
            r#"machine M {
}
machine X {
}
mod t {
    machine F {
    }
    mod x {
        mod y {
            machine R {
            }
        }
    }
}
mod x {
    machine Y {
    }
    mod f {
        machine Y {
        }
    }
    mod r {
        machine T {
        }
    }
}
"#
        );
    }
}
