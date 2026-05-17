use crate::hil::{
    ReturnArity, StructuredFunction,
    cflow::region::RegionNode,
    ir::HilExpr,
    visitor::{Visitor, walk_region},
};

struct ReturnCollector<'a> {
    known: &'a [Option<ReturnArity>],
    signal: Option<ReturnArity>,
}

impl ReturnCollector<'_> {
    fn expr_arity(&self, expr: &HilExpr) -> ReturnArity {
        match expr {
            HilExpr::Call { fun, .. } => self.call_arity(fun),
            HilExpr::MethodCall { .. } => ReturnArity::Unknown,
            HilExpr::VarArgs => ReturnArity::Unknown,
            _ => ReturnArity::Exact(1),
        }
    }

    fn call_arity(&self, fun: &HilExpr) -> ReturnArity {
        let HilExpr::Closure { proto, .. } = fun else {
            return ReturnArity::Unknown;
        };

        match self
            .known
            .get(*proto)
            .copied()
            .flatten()
            .unwrap_or(ReturnArity::Unknown)
        {
            ReturnArity::Exact(n) => ReturnArity::Exact(n),
            ReturnArity::Unknown => ReturnArity::Unknown,
        }
    }

    fn values_arity(&self, values: &[HilExpr]) -> ReturnArity {
        let Some((tail, prefix)) = values.split_last() else {
            return ReturnArity::Exact(0);
        };

        let tail_arity = self.expr_arity(tail);
        match tail_arity {
            ReturnArity::Exact(n) => ReturnArity::Exact(prefix.len() + n),
            ReturnArity::Unknown => ReturnArity::Unknown,
        }
    }

    fn observe_return(&mut self, values: &[HilExpr]) {
        let curr = self.values_arity(values);
        self.signal = Some(match self.signal {
            Some(prev) => prev.merge(curr),
            None => curr,
        });
    }
}

impl Visitor for ReturnCollector<'_> {
    fn visit_region(&mut self, node: &RegionNode) {
        if let RegionNode::Return { values } = node {
            self.observe_return(values);
            return;
        }

        walk_region(self, node);
    }
}

pub fn infer_all(functions: &mut [StructuredFunction]) {
    let mut known = vec![None; functions.len()];

    loop {
        let mut changed = false;

        for fun in functions.iter_mut() {
            let mut collector = ReturnCollector {
                known: &known,
                signal: None,
            };
            collector.visit_region(&fun.root);

            let inferred = collector.signal.unwrap_or(ReturnArity::Exact(0));

            if known[fun.proto] != Some(inferred) {
                known[fun.proto] = Some(inferred);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    for fun in functions {
        fun.return_arity = known[fun.proto];
    }
}

// Not all of these are verified
pub fn luau_global_arity(name: &str) -> ReturnArity {
    match name {
        "assert" => ReturnArity::Unknown,
        "error" => ReturnArity::Unknown,
        "gcinfo" => ReturnArity::Exact(1),
        "getfenv" => ReturnArity::Exact(1),
        "getmetatable" => ReturnArity::Exact(1),
        "ipairs" => ReturnArity::Exact(3),
        "newproxy" => ReturnArity::Exact(1),
        "next" => ReturnArity::Unknown,
        "pairs" => ReturnArity::Exact(3),
        "pcall" => ReturnArity::Unknown,
        "print" => ReturnArity::Unknown,
        "rawequal" => ReturnArity::Exact(1),
        "rawget" => ReturnArity::Exact(1),
        "rawlen" => ReturnArity::Exact(1),
        "rawset" => ReturnArity::Exact(1),
        "select" => ReturnArity::Unknown,
        "setfenv" => ReturnArity::Unknown,
        "setmetatable" => ReturnArity::Exact(1),
        "tonumber" => ReturnArity::Exact(1),
        "tostring" => ReturnArity::Exact(1),
        "type" => ReturnArity::Exact(1),
        "typeof" => ReturnArity::Exact(1),
        "unpack" => ReturnArity::Unknown,
        "xpcall" => ReturnArity::Unknown,

        "math.abs" => ReturnArity::Exact(1),
        "math.acos" => ReturnArity::Exact(1),
        "math.asin" => ReturnArity::Exact(1),
        "math.atan" => ReturnArity::Exact(1),
        "math.atan2" => ReturnArity::Exact(1),
        "math.ceil" => ReturnArity::Exact(1),
        "math.clamp" => ReturnArity::Exact(1),
        "math.cos" => ReturnArity::Exact(1),
        "math.cosh" => ReturnArity::Exact(1),
        "math.deg" => ReturnArity::Exact(1),
        "math.exp" => ReturnArity::Exact(1),
        "math.floor" => ReturnArity::Exact(1),
        "math.fmod" => ReturnArity::Exact(1),
        "math.frexp" => ReturnArity::Exact(2),
        "math.isfinite" => ReturnArity::Exact(1),
        "math.isinf" => ReturnArity::Exact(1),
        "math.isnan" => ReturnArity::Exact(1),
        "math.ldexp" => ReturnArity::Exact(1),
        "math.lerp" => ReturnArity::Exact(1),
        "math.log" => ReturnArity::Exact(1),
        "math.log10" => ReturnArity::Exact(1),
        "math.map" => ReturnArity::Exact(1),
        "math.max" => ReturnArity::Exact(1),
        "math.min" => ReturnArity::Exact(1),
        "math.modf" => ReturnArity::Exact(2),
        "math.noise" => ReturnArity::Exact(1),
        "math.pow" => ReturnArity::Exact(1),
        "math.rad" => ReturnArity::Exact(1),
        "math.random" => ReturnArity::Exact(1),
        "math.randomseed" => ReturnArity::Unknown,
        "math.round" => ReturnArity::Exact(1),
        "math.sign" => ReturnArity::Exact(1),
        "math.sin" => ReturnArity::Exact(1),
        "math.sinh" => ReturnArity::Exact(1),
        "math.sqrt" => ReturnArity::Exact(1),
        "math.tan" => ReturnArity::Exact(1),
        "math.tanh" => ReturnArity::Exact(1),

        "string.byte" => ReturnArity::Unknown,
        "string.char" => ReturnArity::Exact(1),
        "string.find" => ReturnArity::Unknown,
        "string.format" => ReturnArity::Exact(1),
        "string.gmatch" => ReturnArity::Exact(1),
        "string.gsub" => ReturnArity::Exact(2),
        "string.len" => ReturnArity::Exact(1),
        "string.lower" => ReturnArity::Exact(1),
        "string.match" => ReturnArity::Unknown,
        "string.rep" => ReturnArity::Exact(1),
        "string.reverse" => ReturnArity::Exact(1),
        "string.split" => ReturnArity::Exact(1),
        "string.sub" => ReturnArity::Exact(1),
        "string.upper" => ReturnArity::Exact(1),

        "table.clear" => ReturnArity::Unknown,
        "table.clone" => ReturnArity::Exact(1),
        "table.concat" => ReturnArity::Exact(1),
        "table.create" => ReturnArity::Exact(1),
        "table.find" => ReturnArity::Exact(1),
        "table.foreach" => ReturnArity::Unknown,
        "table.foreachi" => ReturnArity::Unknown,
        "table.freeze" => ReturnArity::Exact(1),
        "table.getn" => ReturnArity::Exact(1),
        "table.insert" => ReturnArity::Unknown,
        "table.isfrozen" => ReturnArity::Exact(1),
        "table.maxn" => ReturnArity::Exact(1),
        "table.move" => ReturnArity::Exact(1),
        "table.pack" => ReturnArity::Exact(1),
        "table.remove" => ReturnArity::Exact(1),
        "table.sort" => ReturnArity::Unknown,
        "table.unpack" => ReturnArity::Unknown,

        "bit32.arshift" => ReturnArity::Exact(1),
        "bit32.band" => ReturnArity::Exact(1),
        "bit32.bnot" => ReturnArity::Exact(1),
        "bit32.bor" => ReturnArity::Exact(1),
        "bit32.btest" => ReturnArity::Exact(1),
        "bit32.bxor" => ReturnArity::Exact(1),
        "bit32.byteswap" => ReturnArity::Exact(1),
        "bit32.countlz" => ReturnArity::Exact(1),
        "bit32.countrz" => ReturnArity::Exact(1),
        "bit32.extract" => ReturnArity::Exact(1),
        "bit32.lrotate" => ReturnArity::Exact(1),
        "bit32.lshift" => ReturnArity::Exact(1),
        "bit32.replace" => ReturnArity::Exact(1),
        "bit32.rrotate" => ReturnArity::Exact(1),
        "bit32.rshift" => ReturnArity::Exact(1),

        "os.clock" => ReturnArity::Exact(1),
        "os.date" => ReturnArity::Exact(1),
        "os.difftime" => ReturnArity::Exact(1),
        "os.time" => ReturnArity::Exact(1),

        "coroutine.close" => ReturnArity::Unknown,
        "coroutine.create" => ReturnArity::Exact(1),
        "coroutine.isyieldable" => ReturnArity::Exact(1),
        "coroutine.resume" => ReturnArity::Unknown,
        "coroutine.running" => ReturnArity::Exact(1),
        "coroutine.status" => ReturnArity::Exact(1),
        "coroutine.wrap" => ReturnArity::Exact(1),
        "coroutine.yield" => ReturnArity::Unknown,

        "debug.info" => ReturnArity::Unknown,
        "debug.traceback" => ReturnArity::Exact(1),

        "utf8.char" => ReturnArity::Exact(1),
        "utf8.charpattern" => ReturnArity::Exact(1),
        "utf8.codes" => ReturnArity::Exact(3),
        "utf8.codepoint" => ReturnArity::Unknown,
        "utf8.len" => ReturnArity::Unknown,
        "utf8.offset" => ReturnArity::Exact(1),

        "buffer.readi8" => ReturnArity::Exact(1),
        "buffer.readu8" => ReturnArity::Exact(1),
        "buffer.readi16" => ReturnArity::Exact(1),
        "buffer.readu16" => ReturnArity::Exact(1),
        "buffer.readi32" => ReturnArity::Exact(1),
        "buffer.readu32" => ReturnArity::Exact(1),
        "buffer.readf32" => ReturnArity::Exact(1),
        "buffer.readf64" => ReturnArity::Exact(1),
        "buffer.writei8" => ReturnArity::Unknown,
        "buffer.writeu8" => ReturnArity::Unknown,
        "buffer.writei16" => ReturnArity::Unknown,
        "buffer.writeu16" => ReturnArity::Unknown,
        "buffer.writei32" => ReturnArity::Unknown,
        "buffer.writeu32" => ReturnArity::Unknown,
        "buffer.writef32" => ReturnArity::Unknown,
        "buffer.writef64" => ReturnArity::Unknown,

        "vector.abs" => ReturnArity::Exact(1),
        "vector.angle" => ReturnArity::Exact(1),
        "vector.ceil" => ReturnArity::Exact(1),
        "vector.clamp" => ReturnArity::Exact(1),
        "vector.create" => ReturnArity::Exact(1),
        "vector.cross" => ReturnArity::Exact(1),
        "vector.dot" => ReturnArity::Exact(1),
        "vector.floor" => ReturnArity::Exact(1),
        "vector.lerp" => ReturnArity::Exact(1),
        "vector.magnitude" => ReturnArity::Exact(1),
        "vector.max" => ReturnArity::Exact(1),
        "vector.min" => ReturnArity::Exact(1),
        "vector.normalize" => ReturnArity::Exact(1),
        "vector.sign" => ReturnArity::Exact(1),

        _ => ReturnArity::Unknown,
    }
}
