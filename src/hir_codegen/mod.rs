//! A temporary way to compile pebble until MIR is sorted out.

use crate::{
    hir::{ArraySeg, BinaryOp, ExprId, ExprKind, Hir, Lit, Param, UnaryOp},
    symbol::Symbol,
    ty::{Ty, TyKind},
};
use std::fmt::Write as _;

pub fn codegen(hir: &Hir) -> String {
    let mut codegen = Codegen { f: String::new(), hir };
    for expr in &hir.root {
        expr.generate(&mut codegen);
    }
    codegen.f
}

struct Codegen<'hir> {
    hir: &'hir Hir,
    f: String,
}

trait Gen {
    fn generate(&self, codegen: &mut Codegen);
}

impl Gen for ExprId {
    fn generate(&self, codegen: &mut Codegen) {
        let expr = &codegen.hir.exprs[*self];
        match &expr.kind {
            ExprKind::Break => "break".generate(codegen),
            ExprKind::Ident(ident) => ident.as_str().generate(codegen),
            ExprKind::Literal(lit) => match lit {
                Lit::Abort => r#"panic!("abort")"#.generate(codegen),
                Lit::Unit => "()".generate(codegen),
                Lit::Bool(bool) => _ = write!(codegen.f, "{bool}"),
                Lit::Int(int) => _ = write!(codegen.f, "{int}i64"),
                Lit::Char(char) => _ = write!(codegen.f, "{char:?}"),
                Lit::String(str) => _ = write!(codegen.f, "ArcStr::from({str:?})"),
                Lit::Array { segments } => segments.as_slice().generate(codegen),
            },
            ExprKind::FnDecl { ident, params, ret, body } => {
                ("fn ", ident, params.as_slice(), "->", ret, body.as_slice()).generate(codegen);
            }
            ExprKind::Let { ident, expr } => {
                ("let ", ident, ':', type_of(*expr), '=', expr).generate(codegen);
            }
            ExprKind::Loop(exprs) => ("loop ", exprs.as_slice()).generate(codegen),
            ExprKind::If { arms, els } => {
                for (i, arm) in arms.iter().enumerate() {
                    ((i != 0).then_some("else "), "if ", arm.condition, arm.body.as_slice())
                        .generate(codegen);
                }
                if !els.is_empty() {
                    ("else ", els.as_slice()).generate(codegen);
                }
            }
            ExprKind::Unary { op, expr } => ('(', op, expr, ')').generate(codegen),
            ExprKind::Binary { lhs, op, rhs } => ('(', lhs, op, rhs, ')').generate(codegen),
            ExprKind::FnCall { function, args } => {
                (function, '(').generate(codegen);
                for arg in args {
                    (arg, ',').generate(codegen);
                }
                (')').generate(codegen);
            }
            ExprKind::Index { expr, index } => {
                (expr, '[', index, ']').generate(codegen);
            }
            ExprKind::Block(exprs) => exprs.generate(codegen),
        }
    }
}

impl Gen for BinaryOp {
    fn generate(&self, codegen: &mut Codegen) {
        (match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::Assign => "=",
            Self::AddAssign => "+=",
            Self::SubAssign => "-=",
            Self::MulAssign => "*=",
            Self::DivAssign => "/=",
            Self::ModAssign => "%=",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Greater => ">",
            Self::Less => "<",
            Self::GreaterEq => ">=",
            Self::LessEq => "<=",
            Self::Range => "..",
            Self::RangeInclusive => "..=",
        })
        .generate(codegen);
    }
}

impl Gen for UnaryOp {
    fn generate(&self, codegen: &mut Codegen) {
        (match self {
            Self::Neg => "-",
            Self::Not => "!",
        })
        .generate(codegen);
    }
}

impl Gen for [ArraySeg] {
    fn generate(&self, codegen: &mut Codegen) {
        "{let mut _temp=vec![];".generate(codegen);

        for seg in self {
            let Some(repeated) = seg.repeated else {
                return (seg.expr, ',').generate(codegen);
            };
            (
                "_temp.extend(::std::iter::repeat_with(|| ",
                seg.expr,
                ").take(usize::try_from(",
                repeated,
                ").unwrap()));",
            )
                .generate(codegen);
        }
        "_temp}".generate(codegen);
    }
}

impl Gen for [Param] {
    fn generate(&self, codegen: &mut Codegen) {
        ('(').generate(codegen);
        for param in self {
            (param.ident, ':', &param.ty, ',').generate(codegen);
        }
        (')').generate(codegen);
    }
}

impl Gen for [ExprId] {
    fn generate(&self, codegen: &mut Codegen) {
        '{'.generate(codegen);
        for (i, &expr) in self.iter().enumerate() {
            let exprkind = &codegen.hir.exprs[expr].kind;
            let no_semicolon = i == self.len() - 1 || matches!(exprkind, ExprKind::FnDecl { .. });
            (expr, (!no_semicolon).then_some(';'), "\n").generate(codegen);
        }
        '}'.generate(codegen);
    }
}

impl Gen for Ty {
    fn generate(&self, codegen: &mut Codegen) {
        match self.kind() {
            TyKind::Never => "!".generate(codegen),
            TyKind::Unit => "()".generate(codegen),
            TyKind::Bool => "bool".generate(codegen),
            TyKind::Int => "i64".generate(codegen),
            TyKind::Char => "char".generate(codegen),
            TyKind::Str => "ArcStr".generate(codegen),
            TyKind::Range => "Range<i64>".generate(codegen),
            TyKind::RangeInclusive => "RangeInclusive<i64>".generate(codegen),
            TyKind::Function { .. } => "_".generate(codegen),
            TyKind::Array(array) => ("Vec<", array, ">").generate(codegen),
            TyKind::Infer(..) => unreachable!(),
        }
    }
}

impl Gen for char {
    fn generate(&self, codegen: &mut Codegen) {
        codegen.f.push(*self);
    }
}

impl Gen for str {
    fn generate(&self, codegen: &mut Codegen) {
        codegen.f.push_str(self);
    }
}

impl Gen for Symbol {
    fn generate(&self, codegen: &mut Codegen) {
        codegen.f.push_str(self);
    }
}

macro_rules! impl_tuples {
    ($(($($T:ident),+ $(,)?)),+ $(,)?) => {
        $(impl<$($T: Gen),+> Gen for ($($T,)+) {
            fn generate(&self, codegen: &mut Codegen) {
                #[allow(non_snake_case)]
                let ($($T,)+) = self;
                $($T.generate(codegen));+
            }
        })*
    };
}

impl_tuples!(
    (A,),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F),
    (A, B, C, D, E, F, G),
    (A, B, C, D, E, F, G, H),
);

impl<T: Gen + ?Sized> Gen for &T {
    fn generate(&self, codegen: &mut Codegen) {
        T::generate(self, codegen);
    }
}

impl<T: Gen> Gen for Option<T> {
    fn generate(&self, codegen: &mut Codegen) {
        if let Some(t) = self {
            t.generate(codegen);
        }
    }
}

fn type_of(expr: ExprId) -> impl Gen {
    struct TypeOf(ExprId);
    impl Gen for TypeOf {
        fn generate(&self, codegen: &mut Codegen) {
            codegen.hir.exprs[self.0].ty.generate(codegen);
        }
    }
    TypeOf(expr)
}
