//! Renames emitted locals after the AST is built.
//!
//! Generated local names are unique across the whole emitted program, so one name
//! identifies exactly one binding. Each replacement name is also made unique across
//! the program, which means a renamed local can neither shadow nor be shadowed by
//! any other variable, global or local.

use smol_str::{SmolStr, format_smolstr};

use crate::ast::visitor::VisitorMut;
use crate::ast::{Block, Identifier};
use crate::collections::{HashMap, HashSet};
use crate::common::is_valid_luau_identifier;

/// Outcome of one batch of rename requests.
#[derive(Debug, Clone, Default)]
pub struct RenameReport {
    /// Applied renames as `(old, new)` pairs. The new name may carry a suffix that
    /// keeps it unique.
    pub applied: Vec<(String, String)>,
    /// Requests that were ignored.
    pub skipped: Vec<SkippedRename>,
}

/// One rename request that was ignored.
#[derive(Debug, Clone)]
pub struct SkippedRename {
    /// The requested old name.
    pub from: String,
    /// The requested new name.
    pub to: String,
    /// Why the request was ignored.
    pub reason: &'static str,
}

/// Declared names and every variable-position name in one program.
#[derive(Default)]
struct NameCollector {
    /// Names declared by the program.
    bound: HashSet<SmolStr>,
    /// Every name used as a variable, declared or referenced.
    used: HashSet<SmolStr>,
}

impl NameCollector {
    /// Collects every name in a block.
    fn in_block(block: &mut Block) -> Self {
        let mut collector = Self::default();
        collector.visit_block(block);
        collector
    }

    /// Returns whether a name may be renamed, or why not.
    fn check(&self, name: &str) -> Result<(), &'static str> {
        if !self.bound.contains(name) {
            return Err("not a local declared by the program");
        }
        // `_` and `__mallow_*` are the only names the emitter may declare in more
        // than one function, so excluding them keeps every renamable name unique.
        if name.starts_with('_') {
            return Err("reserved by the decompiler");
        }
        Ok(())
    }
}

impl VisitorMut for NameCollector {
    fn visit_binding(&mut self, name: &mut Identifier) {
        self.bound.insert(name.0.clone());
        self.used.insert(name.0.clone());
    }

    fn visit_reference(&mut self, name: &mut Identifier) {
        self.used.insert(name.0.clone());
    }
}

/// Rewrites every binding and reference of the renamed locals.
struct Renamer {
    renames: HashMap<SmolStr, SmolStr>,
}

impl Renamer {
    fn rename(&self, name: &mut Identifier) {
        if let Some(new) = self.renames.get(&name.0) {
            name.0 = new.clone();
        }
    }
}

impl VisitorMut for Renamer {
    fn visit_binding(&mut self, name: &mut Identifier) {
        self.rename(name);
    }

    fn visit_reference(&mut self, name: &mut Identifier) {
        self.rename(name);
    }
}

/// Returns the local names that `rename_locals` accepts, in no particular order.
pub(crate) fn renamable_locals(block: &mut Block) -> Vec<String> {
    let names = NameCollector::in_block(block);
    names
        .bound
        .iter()
        .filter(|name| names.check(name).is_ok())
        .map(|name| name.to_string())
        .collect()
}

/// Applies the valid requests and reports the rest.
pub(crate) fn rename_locals(
    block: &mut Block,
    requests: impl IntoIterator<Item = (String, String)>,
) -> RenameReport {
    let mut census = NameCollector::in_block(block);
    let mut report = RenameReport::default();

    // The LLM prompt already asks for these rules, but model output is untrusted and a
    // bad rename silently changes which variable a name refers to, so enforce them here.

    // `check` only reads `bound`, so `used` can be moved out.
    let mut used = std::mem::take(&mut census.used);
    let mut renames = HashMap::default();
    for (from, to) in requests {
        let reason = if from == to {
            continue;
        } else if let Err(reason) = census.check(&from) {
            reason
        } else if !is_valid_luau_identifier(&to) {
            "not a valid Luau identifier"
        } else if renames.contains_key(from.as_str()) {
            "requested more than once"
        } else {
            let new = claim_unique(&mut used, SmolStr::new(&to));
            report.applied.push((from.clone(), new.to_string()));
            renames.insert(SmolStr::new(from), new);
            continue;
        };
        report.skipped.push(SkippedRename { from, to, reason });
    }

    if !renames.is_empty() {
        Renamer { renames }.visit_block(block);
    }
    report
}

/// Claims a program-wide unique name, suffixing it on collision.
fn claim_unique(used: &mut HashSet<SmolStr>, preferred: SmolStr) -> SmolStr {
    // I am aware the logic of this is duplicated from the emitter but the use cases are
    // different enough that generalizing them makes no sense.
    if used.insert(preferred.clone()) {
        return preferred;
    }
    for suffix in 1usize.. {
        let candidate = format_smolstr!("{preferred}_{suffix}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("usize overflowed")
}

#[cfg(test)]
mod test {
    use crate::ast::*;
    use crate::rename::*;

    #[test]
    fn renames_bound_variables() {
        let mut block = Block {
            stmts: vec![Stmt::LocalDeclaration {
                names: vec![Typed::untyped(Identifier::new("v0"))],
                values: vec![Expr::Literal(Literal::Float(123.0))],
            }],
        };

        let requests = vec![("v0".to_string(), "foo".to_string())];
        rename_locals(&mut block, requests);

        let Stmt::LocalDeclaration { names, .. } = &block.stmts[0] else {
            unreachable!("first statement is a LocalDeclaration");
        };

        assert_eq!(names[0].as_ref(), &Identifier::new("foo"));
    }

    #[test]
    fn renames_used_variables() {
        let mut block = Block {
            stmts: vec![Stmt::GenericFor {
                vars: vec![
                    Identifier::new("v0"),
                    Identifier::new("v1"),
                    Identifier::new("v2"),
                ],
                exprs: vec![Expr::Named(Identifier::new("some_table"))],
                body: Block::with_stmts(Vec::new()),
            }],
        };

        let requests = vec![
            ("v0".to_string(), "a".to_string()),
            ("v1".to_string(), "b".to_string()),
            ("v2".to_string(), "c".to_string()),
        ];
        rename_locals(&mut block, requests);

        let Stmt::GenericFor { vars, .. } = &block.stmts[0] else {
            unreachable!("first statement is a GenericFor");
        };

        assert_eq!(vars[0], Identifier::new("a"));
        assert_eq!(vars[1], Identifier::new("b"));
        assert_eq!(vars[2], Identifier::new("c"));
    }
}
