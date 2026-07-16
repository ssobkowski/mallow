use std::fmt::Display;

/// A Luau binary operator shared by the compiler representations.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    Eq,
    Ne,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    Concat,
}

impl BinOp {
    /// Returns the Luau source spelling of this operator.
    pub const fn as_str(&self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::IDiv => "//",
            BinOp::Mod => "%",
            BinOp::Pow => "^",
            BinOp::Eq => "==",
            BinOp::Ne => "~=",
            BinOp::Lt => "<",
            BinOp::Lte => "<=",
            BinOp::Gt => ">",
            BinOp::Gte => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Concat => "..",
        }
    }

    /// Returns the Luau precedence level of this binary operator.
    pub const fn precedence(&self) -> u8 {
        match self {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => 3,
            BinOp::Concat => 4,
            BinOp::Add | BinOp::Sub => 5,
            BinOp::Mul | BinOp::Div | BinOp::IDiv | BinOp::Mod => 6,
            BinOp::Pow => 8,
        }
    }

    /// Returns the logical inverse of a comparison operator.
    ///
    /// Non-comparison operators have no logical inverse and return `None`.
    pub const fn invert(self) -> Option<Self> {
        match self {
            BinOp::Eq => Some(BinOp::Ne),
            BinOp::Ne => Some(BinOp::Eq),
            BinOp::Lt => Some(BinOp::Gte),
            BinOp::Lte => Some(BinOp::Gt),
            BinOp::Gt => Some(BinOp::Lte),
            BinOp::Gte => Some(BinOp::Lt),
            _ => None,
        }
    }

    /// Returns the equivalent comparison after swapping its operands.
    ///
    /// Non-comparison operators cannot be flipped and return `None`.
    pub const fn flip(self) -> Option<Self> {
        match self {
            BinOp::Eq => Some(BinOp::Eq),
            BinOp::Ne => Some(BinOp::Ne),
            BinOp::Lt => Some(BinOp::Gt),
            BinOp::Lte => Some(BinOp::Gte),
            BinOp::Gt => Some(BinOp::Lt),
            BinOp::Gte => Some(BinOp::Lte),
            _ => None,
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// A Luau compound-assignment operator.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CompoundBinOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    Concat,
}

impl CompoundBinOp {
    /// Returns the Luau source spelling of this compound-assignment operator.
    pub const fn as_str(&self) -> &'static str {
        match self {
            CompoundBinOp::Add => "+=",
            CompoundBinOp::Sub => "-=",
            CompoundBinOp::Mul => "*=",
            CompoundBinOp::Div => "/=",
            CompoundBinOp::IDiv => "//=",
            CompoundBinOp::Mod => "%=",
            CompoundBinOp::Pow => "^=",
            CompoundBinOp::Concat => "..=",
        }
    }
}

impl Display for CompoundBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl TryFrom<BinOp> for CompoundBinOp {
    type Error = ();

    /// Converts a binary operator into its compound-assignment form.
    fn try_from(op: BinOp) -> Result<Self, Self::Error> {
        match op {
            BinOp::Add => Ok(CompoundBinOp::Add),
            BinOp::Sub => Ok(CompoundBinOp::Sub),
            BinOp::Mul => Ok(CompoundBinOp::Mul),
            BinOp::Div => Ok(CompoundBinOp::Div),
            BinOp::IDiv => Ok(CompoundBinOp::IDiv),
            BinOp::Mod => Ok(CompoundBinOp::Mod),
            BinOp::Pow => Ok(CompoundBinOp::Pow),
            BinOp::Concat => Ok(CompoundBinOp::Concat),
            _ => Err(()),
        }
    }
}

/// A Luau unary operator shared by the compiler representations.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnOp {
    Minus,
    Length,
    Not,
}

impl UnOp {
    /// Returns the Luau source spelling of this unary operator.
    pub const fn as_str(&self) -> &'static str {
        match self {
            UnOp::Minus => "-",
            UnOp::Length => "#",
            UnOp::Not => "not",
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
