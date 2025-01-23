use std::{
    fmt::{Display, Formatter, Result},
    iter::once,
};

use itertools::Itertools;

use crate::{
    asm_analysis::{combine_flags, Module, StatementReference},
    indent,
    parsed::asm::{AbsoluteSymbolPath, SymbolPath},
    write_indented_by, write_items_indented, writeln_indented_by,
};

use super::{
    AnalysisASMFile, AssignmentStatement, CallableSymbol, CallableSymbolDefinitionRef,
    DebugDirective, FunctionBody, FunctionStatement, FunctionStatements, Incompatible,
    IncompatibleSet, InstructionDefinitionStatement, InstructionStatement, LabelStatement,
    LinkDefinition, Machine, MachineDegree, RegisterDeclarationStatement, RegisterTy, Return, Rom,
    SubmachineDeclaration,
};

impl Display for AnalysisASMFile {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write_module(f, self, &AbsoluteSymbolPath::default(), 0)
    }
}

fn write_module(
    f: &mut Formatter<'_>,
    file: &AnalysisASMFile,
    module_path: &AbsoluteSymbolPath,
    indentation: usize,
) -> Result {
    let module: &Module = &file.modules[module_path];
    let mut pil = module.statements.iter();

    for r in &module.ordering {
        match r {
            StatementReference::MachineDeclaration(name) => write_indented_by(
                f,
                format!("machine {name}{}", module.machines[name]),
                indentation,
            ),
            StatementReference::Pil => {
                writeln_indented_by(f, format!("{}", pil.next().unwrap()), indentation)
            }
            StatementReference::Module(name) => {
                let path = module_path
                    .clone()
                    .join(SymbolPath::from_identifier(name.to_string()));
                writeln_indented_by(f, format!("mod {name} {{"), indentation)?;
                write_module(f, file, &path, indentation + 1)?;
                writeln_indented_by(f, "}", indentation)
            }
        }?;
    }

    assert!(pil.next().is_none());

    Ok(())
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
        let params = &self.params.0;
        if !params.is_empty() {
            write!(f, "({params}) ", params = params.iter().format(", "))?;
        }
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
        write!(
            f,
            "{} {}{}",
            self.ty,
            self.name,
            (!self.args.is_empty())
                .then(|| format!("({})", self.args.iter().format(", ")))
                .unwrap_or_default()
        )
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

impl Display for CallableSymbolDefinitionRef<'_> {
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
    use crate::{
        asm_analysis::{Module, StatementReference},
        parsed::asm::parse_absolute_path,
    };
    use pretty_assertions::assert_eq;

    #[test]
    fn display_asm_analysis_file() {
        let file = AnalysisASMFile {
            modules: [
                (
                    "::",
                    vec![
                        StatementReference::MachineDeclaration("M".into()),
                        StatementReference::MachineDeclaration("X".into()),
                        StatementReference::Module("t".into()),
                        StatementReference::Module("x".into()),
                    ],
                ),
                (
                    "::t",
                    vec![
                        StatementReference::MachineDeclaration("F".into()),
                        StatementReference::Module("x".into()),
                    ],
                ),
                (
                    "::x",
                    vec![
                        StatementReference::MachineDeclaration("Y".into()),
                        StatementReference::Module("f".into()),
                        StatementReference::Module("r".into()),
                    ],
                ),
                ("::t::x", vec![StatementReference::Module("y".into())]),
                (
                    "::t::x::y",
                    vec![StatementReference::MachineDeclaration("R".into())],
                ),
                (
                    "::x::f",
                    vec![StatementReference::MachineDeclaration("Y".into())],
                ),
                (
                    "::x::r",
                    vec![StatementReference::MachineDeclaration("T".into())],
                ),
            ]
            .into_iter()
            .map(|(path, ordering)| {
                (
                    parse_absolute_path(path),
                    Module {
                        machines: ordering
                            .iter()
                            .filter_map(|r| match r {
                                StatementReference::MachineDeclaration(name) => {
                                    Some((name.clone(), Machine::default()))
                                }
                                StatementReference::Pil => unimplemented!(),
                                StatementReference::Module(_) => None,
                            })
                            .collect(),
                        ordering,
                        ..Default::default()
                    },
                )
            })
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
