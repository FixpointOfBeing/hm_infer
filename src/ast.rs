use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    TyBool,
    TyNat,
    TyArrow(Box<Type>, Box<Type>),
    TyPair(Box<Type>, Box<Type>),
    TyVar(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub vars: Vec<String>,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Nat(usize),
    Bool(bool),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    IsZero(Box<Expr>),
    Succ(Box<Expr>),
    Pair(Box<Expr>, Box<Expr>),
    PairFst(Box<Expr>),
    PairSnd(Box<Expr>),
    Var(String),
    Lambda(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
}
impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::TyBool => write!(f, "Bool"),
            Type::TyNat => write!(f, "Nat"),
            Type::TyArrow(arg_ty, ret_ty) => write!(f, "({} -> {})", arg_ty, ret_ty),
            Type::TyPair(fst_ty, snd_ty) => write!(f, "({} , {})", fst_ty, snd_ty),
            Type::TyVar(name) => write!(f, "{}", name),
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Nat(n) => write!(f, "{}", n),
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::If(pred, conseq, alt) => write!(f, "if {} then {} else {}", pred, conseq, alt),
            Expr::IsZero(expr) => write!(f, "zero? {}", expr),
            Expr::Succ(expr) => write!(f, "succ {}", expr),
            Expr::Pair(fst, snd) => write!(f, "({}, {})", fst, snd),
            Expr::PairFst(expr) => write!(f, "fst {}", expr),
            Expr::PairSnd(expr) => write!(f, "snd {}", expr),
            Expr::Var(name) => write!(f, "{}", name),
            Expr::Lambda(param, body) => write!(f, "\\{} => {}", param, body),
            Expr::App(fun, arg) => write!(f, "{} {}", fun, arg),
            Expr::Let(binding, rhs, body) => write!(f, "let {} = {} in {}", binding, rhs, body),
        }
    }
}