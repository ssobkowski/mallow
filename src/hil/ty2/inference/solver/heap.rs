//! Shared mutable-table allocation mechanics.

use std::collections::{HashMap, HashSet};

use smol_str::SmolStr;

use super::model::{InferenceVarId, TableField, TableObject, TableObjectId, TypeSolver};
use crate::hil::ty2::inference::program::TableKey;

impl TypeSolver<'_> {
    /// Returns or allocates the mutable table object for one collected allocation.
    pub(super) fn table_for_key(&mut self, key: TableKey) -> TableObjectId {
        if let Some(table) = self.tables_by_key.get(&key) {
            return *table;
        }
        let keys = self.fresh_variable();
        let values = self.fresh_variable();
        let table = self.tables.alloc(TableObject {
            keys,
            values,
            fields: HashMap::new(),
            metatables: HashSet::new(),
        });
        self.tables_by_key.insert(key, table);
        table
    }

    /// Returns or creates the variable for one named table field.
    pub(super) fn table_field_variable(
        &mut self,
        table: TableObjectId,
        field: SmolStr,
        definite: bool,
    ) -> InferenceVarId {
        if let Some(existing) = self.tables[table].fields.get_mut(&field) {
            existing.definite |= definite;
            return existing.value;
        }
        let value = self.fresh_variable();
        self.tables[table]
            .fields
            .insert(field, TableField { value, definite });
        value
    }

    /// Re-enqueues every variable carrying a changed table allocation.
    pub(super) fn table_changed(&mut self, table: TableObjectId) {
        let users = self.table_users.get(&table).cloned().unwrap_or_default();
        for user in users {
            self.variable_changed(user);
        }
    }
}
