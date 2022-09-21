#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SMTVariable {
    pub name: String,
}

impl SMTFormat for SMTVariable {
    fn as_smt(&self) -> String {
        self.name.clone()
    }
}

pub trait SMTFormat {
    fn as_smt(&self) -> String;
}

type BoxedSMTFormat = Box<dyn SMTFormat>;

impl SMTFormat for String {
    fn as_smt(&self) -> String {
        self.to_string()
    }
}

impl SMTFormat for usize {
    fn as_smt(&self) -> String {
        format!("#x{:064x}", self)
    }
}

impl<T: SMTFormat> SMTFormat for Vec<T> {
    fn as_smt(&self) -> String {
        self.iter()
            .map(SMTFormat::as_smt)
            .collect::<Vec<_>>()
            .join(" ")
    }
}

pub enum SMTIdentifier {
    Simple(String),
}

pub enum SMTSort {
    Simple(SMTIdentifier),
    Parametric(SMTIdentifier, Vec<Self>),
}

impl SMTSort {
    pub fn bitvec(index: usize) -> Self {
        Self::Simple(SMTIdentifier::Simple(format!("(_ BitVec {})", index)))
    }
}

pub enum SMTLiteral {
    Hex(String),
}

impl SMTLiteral {
    pub fn bv256_zero() -> Self {
        Self::Hex("0".repeat(64))
    }
}

pub enum SMTExpression {
    Eq(BoxedSMTFormat, BoxedSMTFormat),
    Not(BoxedSMTFormat),
    Literal(SMTLiteral),
    Variable(SMTIdentifier),
}

impl From<u64> for SMTExpression {
    fn from(input: u64) -> SMTExpression {
        SMTExpression::Literal(SMTLiteral::Hex(format!("{:064x}", input)))
    }
}

impl From<SMTVariable> for SMTExpression {
    fn from(input: SMTVariable) -> SMTExpression {
        SMTExpression::Variable(SMTIdentifier::Simple(input.name))
    }
}

pub enum SMTStatement {
    Assert(BoxedSMTFormat),
    DeclareConst(String, SMTSort),
    DefineConst(String, SMTSort, String),
}

macro_rules! impl_smt {
    (enum $type:ident {
        $($variant:ident ( $($field:ident),* $(,)? ) $format:literal),*  $(,)?
    }) => {
        impl SMTFormat for $type {
            fn as_smt(&self) -> String {
                match self {
                    $($type::$variant($($field),*) => format!($format, $($field.as_smt()),*),)*
                }
            }
        }

        impl From<$type> for String {
            fn from(unit: $type) -> String {
                unit.as_smt()
            }
        }
    };
}

macro_rules! impl_smt_expression_constructors {
    ($($function:ident($($field:ident),*): $smt_name:literal ),*) => {
        $(
        pub fn $function($($field: impl SMTFormat),*) -> String {
            let mut formatted = format!("({}", $smt_name);
            $(
                formatted.push(' ');
                formatted.push_str($field.as_smt().as_str());
            )*
            formatted.push(')');
            formatted
        }
        )*
    };
}

impl_smt!(
    enum SMTIdentifier {
        Simple(symbol) "{}",
    }
);
impl_smt!(
    enum SMTSort {
        Simple(ident) "{}",
        Parametric(ident, sorts) "({} {})",
    }
);
impl_smt!(
    enum SMTLiteral {
        Hex(val) "#x{}",
    }
);
impl_smt!(
    enum SMTExpression {
        Eq(lhs, rhs) "(= {} {})",
        Not(inner) "(not {})",
        Literal(l) "{}",
        Variable(v) "{}"
    }
);

impl_smt_expression_constructors!(
    eq(lhs, rhs): "=",
    ite(cond, true_expr, false_expr): "ite",
    not(inner): "not"
);

impl_smt!(
    enum SMTStatement {
        Assert(inner) "(assert {})",
        DeclareConst(symbol, sort) "(declare-const {} {})",
        DefineConst(symbol, sort, term) "(define-const {} {} {})",
    }
);
