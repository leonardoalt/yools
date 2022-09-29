#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SMTSort {
    Bool,
    BV(u64),
    Array(Box<SMTSort>, Box<SMTSort>),
}

pub fn bv(width: u64) -> SMTSort {
    SMTSort::BV(width)
}

pub fn array(index: SMTSort, elem: SMTSort) -> SMTSort {
    SMTSort::Array(Box::new(index), Box::new(elem))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SMTVariable {
    pub name: String,
    pub sort: SMTSort,
}

impl SMTVariable {
    pub fn new(name: String, sort: SMTSort) -> Self {
        SMTVariable { name, sort }
    }
}

/// We keep the SMT expressions loose and runtime based for now.
/// A potential future refactor may add compile time guarantees
/// that illegal expressions cannot be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SMTExpr {
    pub op: SMTOp,
    pub args: Vec<SMTExpr>,
}

impl From<u64> for SMTExpr {
    fn from(input: u64) -> SMTExpr {
        SMTExpr {
            op: SMTOp::Literal(format!("{:064x}", input)),
            args: vec![],
        }
    }
}

impl From<SMTVariable> for SMTExpr {
    fn from(input: SMTVariable) -> SMTExpr {
        SMTExpr {
            op: SMTOp::Variable(input),
            args: vec![],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SMTStatement {
    Assert(SMTExpr),
    DeclareConst(SMTVariable),
    DeclareFun(SMTVariable, Vec<SMTSort>),
    DefineConst(SMTVariable, SMTExpr),
    DefineFun(SMTVariable, Vec<SMTSort>, SMTExpr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SMTOp {
    Eq,
    Not,
    And,
    Or,
    Ite,
    BvNot,
    BvAnd,
    BvOr,
    BvXor,
    BvAdd,
    BvSub,
    BvMul,
    BvUDiv,
    BvSDiv,
    BvURem,
    BvSMod,
    BvULt,
    BvUGt,
    BvSLt,
    BvSGt,
    BvShl,
    BvLShr,
    BvAShr,
    Extract(u64, u64),
    Concat,
    Select,
    Store,
    Literal(String),
    Variable(SMTVariable),
    UF(SMTVariable), // TODO We should have a specialized SMTFunction
}

// SMT expression builders

pub fn eq<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Eq,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn neq<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    not(eq(lhs, rhs))
}

pub fn eq_zero<L: Into<SMTExpr>>(expr: L) -> SMTExpr {
    eq(expr, 0)
}

pub fn neq_zero<L: Into<SMTExpr>>(expr: L) -> SMTExpr {
    neq(expr, 0)
}

pub fn not<L: Into<SMTExpr>>(expr: L) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Not,
        args: vec![expr.into()],
    }
}

pub fn and<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::And,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn and_vec(args: Vec<SMTExpr>) -> SMTExpr {
    SMTExpr {
        op: SMTOp::And,
        args,
    }
}

pub fn or<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Or,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn or_vec(args: Vec<SMTExpr>) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Or,
        args,
    }
}

pub fn ite<C: Into<SMTExpr>, T: Into<SMTExpr>, F: Into<SMTExpr>>(
    cond: C,
    true_term: T,
    false_term: F,
) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Ite,
        args: vec![cond.into(), true_term.into(), false_term.into()],
    }
}

pub fn bvnot<L: Into<SMTExpr>>(expr: L) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvNot,
        args: vec![expr.into()],
    }
}

pub fn bvand<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvAnd,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvor<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvOr,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvxor<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvXor,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvadd<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvAdd,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvsub<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvSub,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvmul<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvMul,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvudiv<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvUDiv,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvsdiv<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvSDiv,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvurem<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvURem,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvsmod<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvSMod,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvult<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvULt,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvugt<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvUGt,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvslt<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvSLt,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvsgt<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvSGt,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvshl<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvShl,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvlshr<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvLShr,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn bvashr<L: Into<SMTExpr>, R: Into<SMTExpr>>(lhs: L, rhs: R) -> SMTExpr {
    SMTExpr {
        op: SMTOp::BvAShr,
        args: vec![lhs.into(), rhs.into()],
    }
}

pub fn extract<L: Into<SMTExpr>>(msb: u64, lsb: u64, expr: L) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Extract(msb, lsb),
        args: vec![expr.into()],
    }
}

pub fn concat(args: Vec<SMTExpr>) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Concat,
        args,
    }
}

pub fn select<A: Into<SMTExpr>, I: Into<SMTExpr>>(arr: A, idx: I) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Select,
        args: vec![arr.into(), idx.into()],
    }
}

pub fn store<A: Into<SMTExpr>, I: Into<SMTExpr>, V: Into<SMTExpr>>(
    arr: A,
    idx: I,
    val: V,
) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Store,
        args: vec![arr.into(), idx.into(), val.into()],
    }
}

pub fn literal(lit: String) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Literal(lit),
        args: vec![],
    }
}

pub fn uf(function: SMTVariable, args: Vec<SMTExpr>) -> SMTExpr {
    SMTExpr {
        op: SMTOp::UF(function),
        args,
    }
}

pub fn literal_12_bytes(n: u64) -> SMTExpr {
    SMTExpr {
        op: SMTOp::Literal(format!("{:024x}", n)),
        args: vec![],
    }
}

// SMT statement builders

pub fn assert(expr: SMTExpr) -> SMTStatement {
    SMTStatement::Assert(expr)
}

pub fn declare_const(var: SMTVariable) -> SMTStatement {
    SMTStatement::DeclareConst(var)
}

pub fn declare_fun(var: SMTVariable, sorts: Vec<SMTSort>) -> SMTStatement {
    SMTStatement::DeclareFun(var, sorts)
}

pub fn define_const(var: SMTVariable, val: SMTExpr) -> SMTStatement {
    SMTStatement::DefineConst(var, val)
}

pub fn define_fun(var: SMTVariable, sorts: Vec<SMTSort>, val: SMTExpr) -> SMTStatement {
    SMTStatement::DefineFun(var, sorts, val)
}

// Format stuff

pub trait SMTFormat {
    fn as_smt(&self) -> String;
}

impl SMTFormat for SMTSort {
    fn as_smt(&self) -> String {
        match self {
            SMTSort::Bool => "Bool".to_string(),
            SMTSort::BV(width) => format!("(_ BitVec {})", width),
            SMTSort::Array(index, elem) => format!("(Array {} {})", index.as_smt(), elem.as_smt()),
        }
    }
}

impl SMTFormat for SMTVariable {
    fn as_smt(&self) -> String {
        self.name.clone()
    }
}

impl SMTFormat for SMTExpr {
    fn as_smt(&self) -> String {
        match &self.op {
            SMTOp::Eq => {
                assert!(self.args.len() == 2);
                format!("(= {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::Not => {
                assert!(self.args.len() == 1);
                format!("(not {})", self.args[0].as_smt())
            }
            SMTOp::And => {
                assert!(self.args.len() >= 2);
                format!("(and {})", self.args.as_smt())
            }
            SMTOp::Or => {
                assert!(self.args.len() >= 2);
                format!("(or {})", self.args.as_smt())
            }
            SMTOp::Ite => {
                assert!(self.args.len() == 3);
                format!(
                    "(ite {} {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt(),
                    self.args[2].as_smt()
                )
            }
            SMTOp::BvNot => {
                assert!(self.args.len() == 1);
                format!("(bvnot {})", self.args[0].as_smt())
            }
            SMTOp::BvAnd => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvand {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvOr => {
                assert!(self.args.len() == 2);
                format!("(bvor {} {})", self.args[0].as_smt(), self.args[1].as_smt())
            }
            SMTOp::BvXor => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvxor {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvAdd => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvadd {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvSub => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvsub {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvMul => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvmul {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvUDiv => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvudiv {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvSDiv => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvsdiv {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvURem => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvurem {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvSMod => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvsmod {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvULt => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvult {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvUGt => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvugt {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvSLt => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvslt {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvSGt => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvsgt {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvShl => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvshl {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvLShr => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvlshr {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::BvAShr => {
                assert!(self.args.len() == 2);
                format!(
                    "(bvashr {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::Extract(msb, lsb) => {
                assert!(self.args.len() == 1);
                format!("((_ extract {} {}) {})", msb, lsb, self.args[0].as_smt())
            }
            SMTOp::Concat => {
                format!("(concat {})", self.args.as_smt())
            }
            SMTOp::Select => {
                assert!(self.args.len() == 2);
                format!(
                    "(select {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt()
                )
            }
            SMTOp::Store => {
                assert!(self.args.len() == 3);
                format!(
                    "(store {} {} {})",
                    self.args[0].as_smt(),
                    self.args[1].as_smt(),
                    self.args[2].as_smt()
                )
            }

            SMTOp::Literal(lit) => format!("#x{}", lit),
            SMTOp::Variable(var) if self.args.is_empty() => var.as_smt(),
            SMTOp::Variable(var) => format!("({} {})", var.as_smt(), self.args.as_smt()),

            SMTOp::UF(function) => {
                format!("({} {})", function.name, self.args.as_smt())
            }
        }
    }
}

impl SMTFormat for SMTStatement {
    fn as_smt(&self) -> String {
        match self {
            SMTStatement::Assert(expr) => format!("(assert {})", expr.as_smt()),
            SMTStatement::DeclareConst(var) => {
                format!("(declare-const {} {})", var.name, var.sort.as_smt())
            }
            SMTStatement::DeclareFun(var, sorts) => format!(
                "(declare-fun {} ({}) {})",
                var.name,
                sorts.as_smt(),
                var.sort.as_smt()
            ),
            SMTStatement::DefineConst(var, expr) => format!(
                "(define-const {} {} {})",
                var.name,
                var.sort.as_smt(),
                expr.as_smt()
            ),
            SMTStatement::DefineFun(var, sorts, expr) => format!(
                "(define-fun {} ({}) {} {})",
                var.name,
                sorts.as_smt(),
                var.sort.as_smt(),
                expr.as_smt()
            ),
        }
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
