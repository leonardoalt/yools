#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SMTVariable {
    pub name: String,
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
        self.to_string()
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
    Indexed(String, Vec<usize>),
}

pub enum SMTSort {
    Simple(SMTIdentifier),
    Parametric(SMTIdentifier, Vec<Self>),
}

impl SMTSort {
    pub fn bitvec(index: usize) -> Self {
        Self::Simple(SMTIdentifier::Indexed("BitVec".to_owned(), vec![index]))
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
    ($($function:ident($($field:ident),*): $variant:ident ),*) => {
        $(
        pub fn $function($($field: impl Into<SMTExpression>),*) -> SMTExpression {
            SMTExpression::$variant($(Box::new($field.into())),*)
        }
        )*
    };
}

impl_smt!(
    enum SMTIdentifier {
        Simple(symbol) "{}",
        Indexed(symbol, index) "(_ {} {})",
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

impl_smt_expression_constructors!(eq(lhs, rhs): Eq, not(inner): Not);

impl_smt!(
    enum SMTStatement {
        Assert(inner) "(assert {})",
        DeclareConst(symbol, sort) "(declare-const {} {})",
        DefineConst(symbol, sort, term) "(define-const {} {} {})",
    }
);
