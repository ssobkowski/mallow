//! Solver-native records and mutable state ownership.

use std::collections::{HashMap, HashSet};

use id_arena::{Arena, Id};
use smol_str::SmolStr;

use crate::{
    hil::{
        lifted::LiftedFunction,
        ty2::{
            builtins::{BuiltinEnvironment, BuiltinPath},
            canonical::TypeId,
            inference::queue::WorkQueue,
            store::TypeStore,
        },
    },
    il::ProtoId,
    operator::{BinOp, UnOp},
};

use super::super::program::{
    GenericFieldCall, GenericValueRelation, PackSlot, TableKey, Truthiness, TypeSlot,
};

/// Stable handle for one solver inference variable.
pub(super) type InferenceVarId = Id<InferenceVariable>;

/// Stable handle for one inference-time value pack.
pub(super) type PackVarId = Id<PackVariable>;

/// Stable handle for one inferred mutable table object.
pub(super) type TableObjectId = Id<TableObject>;

/// Bounds and identity facts associated with one inference variable.
#[derive(Debug, Clone)]
pub(super) struct InferenceVariable {
    /// Union of concrete producer observations.
    pub(super) lower: TypeId,
    /// Intersection of consumer requirements.
    pub(super) upper: TypeId,
    /// Concrete closure identities carried by the value.
    pub(super) closures: HashSet<ProtoId>,
    /// Mutable table identities carried by the value.
    pub(super) tables: HashSet<TableObjectId>,
    /// Builtin schemes carried by the value.
    pub(super) builtins: HashSet<BuiltinPath>,
}

/// One concrete sequence alternative carried by an inference-time pack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PackAlternative {
    /// Values guaranteed at the start of the alternative.
    pub(super) head: Vec<InferenceVarId>,
    /// Remaining sequence, or `None` when the alternative ends after `head`.
    pub(super) tail: Option<PackVarId>,
}

/// Mutable facts and lazily requested views for one value pack.
#[derive(Debug, Default)]
pub(super) struct PackVariable {
    /// Concrete sequence alternatives discovered for the pack.
    pub(super) alternatives: Vec<PackAlternative>,
    /// Homogeneous open sources carried by the pack.
    pub(super) homogeneous: Vec<InferenceVarId>,
    /// Stable scalar projection variables by zero-based position.
    pub(super) projections: HashMap<usize, InferenceVarId>,
    /// Stable aggregate of values that the pack can actually produce.
    pub(super) values: Option<InferenceVarId>,
}

/// One propagation relation applied when a source pack gains an alternative.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum PackUse {
    /// Links the complete source sequence into `target`.
    FlowTo(PackVarId),
    /// Invalidates `target` when a nested tail changes shape.
    ShapeTo(PackVarId),
    /// Copies the source suffix after `skip` values into `target`.
    SuffixTo {
        /// Pack receiving the suffix.
        target: PackVarId,
        /// Number of leading values removed from each source alternative.
        skip: usize,
    },
}

/// One inferred named field in a mutable table object.
#[derive(Debug, Clone, Copy)]
pub(super) struct TableField {
    /// Variable accumulating values written to the field.
    pub(super) value: InferenceVarId,
    /// Whether a table constructor definitely initialized the field.
    pub(super) definite: bool,
}

/// Mutable heap-shape facts for one table allocation.
#[derive(Debug)]
pub(super) struct TableObject {
    /// Variable accumulating dynamic index keys.
    pub(super) keys: InferenceVarId,
    /// Variable accumulating dynamic index values.
    pub(super) values: InferenceVarId,
    /// Named fields observed on the allocation.
    pub(super) fields: HashMap<SmolStr, TableField>,
    /// Table allocations installed as metatables.
    pub(super) metatables: HashSet<TableObjectId>,
}

/// One solver-native constraint referencing arena variables directly.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum SolverConstraint {
    /// Adds a producer observation to the constrained variable.
    Observe(TypeId),
    /// Narrows the constrained variable to a consumer-accepted type.
    Require(TypeId),
    /// Propagates a subtype edge from `source` into the constrained variable.
    FlowFrom(InferenceVarId),
    /// Equates the constrained variable and `other`.
    Equal(InferenceVarId),
    /// Creates a truthiness-filtered occurrence from `source`.
    RefinedFrom {
        /// Unrefined definition variable.
        source: InferenceVarId,
        /// Edge restriction applied to the occurrence.
        truthiness: Truthiness,
    },
    /// Adds one mutable table identity.
    NewTable(TableObjectId),
    /// Applies an indexed write to every known table identity.
    SetIndex {
        /// Index variable.
        index: InferenceVarId,
        /// Written value variable.
        value: InferenceVarId,
    },
    /// Applies every concrete pack element as an indexed write.
    SetIndexPack {
        /// Pack whose produced elements are written at numeric indices.
        values: PackVarId,
    },
    /// Applies an indexed read to every known table identity.
    GetIndex {
        /// Index variable.
        index: InferenceVarId,
        /// Read destination variable.
        value: InferenceVarId,
    },
    /// Applies a named-field write to every known table identity.
    SetField {
        /// Field selected by the write.
        field: SmolStr,
        /// Written value variable.
        value: InferenceVarId,
        /// Whether the constructor definitely initializes the field.
        definite: bool,
    },
    /// Applies a named-field read to every known table identity.
    GetField {
        /// Field selected by the read.
        field: SmolStr,
        /// Read destination variable.
        value: InferenceVarId,
    },
    /// Relates a binary expression's operands and result.
    Binary {
        /// Binary operation.
        op: BinOp,
        /// Right operand variable.
        rhs: InferenceVarId,
        /// Result variable.
        result: InferenceVarId,
    },
    /// Relates a unary expression's operand and result.
    Unary {
        /// Unary operation.
        op: UnOp,
        /// Result variable.
        result: InferenceVarId,
    },
    /// Calls the constrained variable.
    Call {
        /// Pack containing every supplied argument.
        args: PackVarId,
        /// Pack receiving every produced result.
        returns: PackVarId,
    },
    /// Calls one field separately for each concrete receiver table.
    FieldCall {
        /// Field containing the callable value.
        callee: SmolStr,
        /// Fixed argument prefix retaining same-table field provenance.
        head: Vec<SolverCallArgument>,
        /// Optional remaining argument pack.
        tail: Option<PackVarId>,
        /// Pack receiving every produced result.
        returns: PackVarId,
    },
    /// Adds one concrete closure identity.
    Closure(ProtoId),
    /// Adds one builtin scheme identity.
    Builtin(BuiltinPath),
    /// Links table objects through `setmetatable`.
    SetMetatable {
        /// Variable containing metatable identities.
        metatable: InferenceVarId,
        /// Optional destination receiving the base value.
        result: Option<InferenceVarId>,
    },
    /// Observes values stored in a table after excluding deletion-by-`nil`.
    NonNilFrom {
        /// Written value whose `nil` alternative does not remain stored.
        source: InferenceVarId,
    },
    /// Observes a source variable after excluding concrete scheme alternatives.
    GenericFrom {
        /// Argument variable supplying generic evidence.
        source: InferenceVarId,
        /// Concrete union alternatives that do not belong to the generic.
        excluded: Vec<TypeId>,
    },
}

/// One argument to a table-field call after solver lowering.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum SolverCallArgument {
    /// An independently inferred value.
    Value(InferenceVarId),
    /// A field of the same concrete table as the callee.
    Field(SmolStr),
}

/// Constraint plus a stable identity used for one-time dynamic activation.
#[derive(Debug, Clone)]
pub(super) struct ConstraintRecord {
    /// Monotonic identifier within the solver.
    pub(super) id: usize,
    /// Relation applied when the primary variable is processed.
    pub(super) constraint: SolverConstraint,
}

/// One indexed callsite used for closure and builtin activation.
#[derive(Debug, Clone)]
pub(super) struct CallSite {
    /// Variable holding the callable value.
    pub(super) callee: InferenceVarId,
    /// Pack containing every supplied argument.
    pub(super) args: PackVarId,
    /// Pack receiving every produced result.
    pub(super) returns: PackVarId,
}

/// One unresolved refinement retained until ordinary propagation reaches quiescence.
#[derive(Debug, Clone, Copy)]
pub(super) struct DeferredRefinement {
    /// Refined occurrence receiving the conservative fallback.
    pub(super) target: InferenceVarId,
    /// Definition whose producer evidence remained absent.
    pub(super) source: InferenceVarId,
    /// Branch restriction used to derive the fallback type.
    pub(super) truthiness: Truthiness,
}
/// One operator overload resolved only after concrete identity propagation settles.
#[derive(Debug, Clone, Copy)]
pub(super) enum DeferredOperator {
    /// Defaults an otherwise unconstrained arithmetic operation to numbers.
    Arithmetic {
        /// Left operand.
        lhs: InferenceVarId,
        /// Right operand.
        rhs: InferenceVarId,
        /// Produced result.
        result: InferenceVarId,
    },
    /// Narrows a comparison from the concrete primitive used by either side.
    Comparison {
        /// Left operand.
        lhs: InferenceVarId,
        /// Right operand.
        rhs: InferenceVarId,
    },
    /// Defaults an otherwise unconstrained negation to numeric negation.
    UnaryMinus {
        /// Negated operand.
        operand: InferenceVarId,
        /// Produced result.
        result: InferenceVarId,
    },
}

/// Arena-backed bounded constraint solver.
pub(in crate::hil::ty2::inference) struct TypeSolver<'a> {
    /// Canonical graph owned by this inference session.
    pub(super) types: &'a mut TypeStore,
    /// Inference-variable storage.
    pub(super) variables: Arena<InferenceVariable>,
    /// Durable HIL slots mapped to inference variables.
    pub(super) variables_by_slot: HashMap<TypeSlot, InferenceVarId>,
    /// Inference-time value-pack storage.
    pub(super) packs: Arena<PackVariable>,
    /// Durable pack slots mapped to inference packs.
    pub(super) packs_by_slot: HashMap<PackSlot, PackVarId>,
    /// Future propagation uses grouped by their source pack.
    pub(super) pack_uses: HashMap<PackVarId, HashSet<PackUse>>,
    /// Scalar constraints that must rerun when a pack gains shape facts.
    pub(super) pack_dependents: HashMap<PackVarId, HashSet<InferenceVarId>>,
    /// Stable projection and tail-aggregate views prepared for output packs.
    pub(super) output_pack_views: HashMap<PackVarId, (Vec<InferenceVarId>, Option<InferenceVarId>)>,
    /// Constraints grouped by primary variable.
    pub(super) constraints: HashMap<InferenceVarId, Vec<ConstraintRecord>>,
    /// Reverse dependencies used to reschedule affected variables.
    pub(super) dependencies: HashMap<InferenceVarId, HashSet<InferenceVarId>>,
    /// Pending primary variables.
    pub(super) queue: WorkQueue<InferenceVarId>,
    /// Mutable table-object storage.
    pub(super) tables: Arena<TableObject>,
    /// Collected table keys mapped to table-object identities.
    pub(super) tables_by_key: HashMap<TableKey, TableObjectId>,
    /// Variables currently carrying each table identity.
    pub(super) table_users: HashMap<TableObjectId, HashSet<InferenceVarId>>,
    /// Lifted functions indexed by proto ID.
    pub(super) functions: &'a [LiftedFunction],
    /// Shared builtin scheme environment.
    pub(super) builtins: &'a BuiltinEnvironment,
    /// Same-table callback relations recovered for generic source signatures.
    pub(super) generic_field_calls: HashMap<ProtoId, Vec<GenericFieldCall>>,
    /// Direct formal-to-return relations recovered for generic source signatures.
    pub(super) generic_value_relations: HashMap<ProtoId, Vec<GenericValueRelation>>,
    /// Actual argument packs observed for each concrete closure proto.
    pub(super) closure_argument_packs: HashMap<ProtoId, HashSet<PackVarId>>,
    /// Callsites stored by dense call ID.
    pub(super) callsites: Vec<CallSite>,
    /// Dynamic callable requirements waiting for identity propagation to settle.
    pub(super) deferred_callable_requirements: HashMap<usize, CallSite>,
    /// Call IDs grouped by callee variable.
    pub(super) callsites_by_callee: HashMap<InferenceVarId, Vec<usize>>,
    /// Closure targets already connected to a callsite.
    pub(super) activated_closures: HashSet<(usize, ProtoId)>,
    /// Builtin arity and argument-type states already instantiated at each callsite.
    pub(super) activated_builtins: HashSet<(
        usize,
        BuiltinPath,
        usize,
        Option<usize>,
        Vec<Option<TypeId>>,
    )>,
    /// Builtin callsites waiting for stable-arity heap-effect activation.
    pub(super) deferred_builtin_effects: HashSet<(usize, BuiltinPath)>,
    /// Builtin heap effects already activated after ordinary pack propagation settled.
    pub(super) activated_builtin_effects: HashSet<(usize, BuiltinPath)>,
    /// Structural call signatures already connected to one constraint.
    pub(super) activated_call_signatures: HashSet<(usize, TypeId)>,
    /// Table operations already connected to a concrete allocation.
    pub(super) activated_table_constraints: HashSet<(usize, TableObjectId)>,
    /// Index-dispatch handlers already connected for each table read.
    pub(super) activated_index_dispatches: HashSet<(usize, TableObjectId)>,
    /// Named fields already connected to each dynamic table read.
    pub(super) activated_dynamic_fields: HashSet<(usize, TableObjectId, SmolStr)>,
    /// Refinements waiting for producer-free fallback after normal quiescence.
    pub(super) deferred_refinements: HashMap<usize, DeferredRefinement>,
    /// Refinement records whose producer-free fallback has run once.
    pub(super) activated_refinement_fallbacks: HashSet<usize>,
    /// Operators waiting for primitive fallback after identity propagation.
    pub(super) deferred_operators: HashMap<usize, DeferredOperator>,
    /// Operator records whose primitive fallback decision has run once.
    pub(super) activated_operator_fallbacks: HashSet<usize>,
    /// Next stable constraint identity.
    pub(super) next_constraint_id: usize,
}
