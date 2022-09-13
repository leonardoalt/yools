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
    }
);
impl_smt!(
    enum SMTStatement {
        Assert(inner) "(assert {})",
        DeclareConst(symbol, sort) "(declare-const {} {})",
        DefineConst(symbol, sort, term) "(define-const {} {} {})",
    }
);
