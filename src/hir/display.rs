use std::{
    fmt::{self, Write},
    mem,
};

use super::{ArraySeg, ExprKind, FnDecl, MatchArm, OpAssign, Param, Pat};
use crate::{
    hir::{BinaryOp, ExprId, Hir, Lit, UnaryOp},
    symbol::Symbol,
    ty::{Ty, TyCtx},
};

struct Writer<'a, 'tcx> {
    hir: &'a Hir<'a>,
    tcx: &'tcx TyCtx<'tcx>,
    f: String,
    indent: usize,
    inside_expr: bool,
}

impl Hir<'_> {
    pub fn display<'tcx>(&self, tcx: &'tcx TyCtx<'tcx>) -> impl fmt::Display {
        let f = String::new();
        let mut w = Writer { hir: self, f, indent: 0, inside_expr: false, tcx };
        self.root.iter().for_each(|expr| (expr, Line).write(&mut w));
        w.f
    }
}

impl Dump for MatchArm {
    fn write(&self, w: &mut Writer) {
        (&self.pat, " => ", self.body).write(w);
    }
}

impl Dump for Pat {
    fn write(&self, w: &mut Writer) {
        match *self {
            Self::Ident(ident) => ident.write(w),
            Self::Str(str) => Lit::String(str).write(w),
            Self::Int(int) => Lit::Int(int).write(w),
            Self::Or(ref patterns) => Sep(patterns, " | ").write(w),
        }
    }
}

impl Writer<'_, '_> {
    fn display_expr(&mut self, expr: ExprId) {
        let inside_expr = mem::replace(&mut self.inside_expr, true);
        match self.hir.exprs[expr].kind {
            ExprKind::Match { scrutinee, ref arms } => {
                ("match ", scrutinee, " {").write(self);
                self.indent += 1;
                (Line, Sep(arms, (",", Line))).write(self);
                self.indent -= 1;
                (Line, "}").write(self);
            }
            ExprKind::Loop(ref block) => ("loop ", block.as_slice()).write(self),
            ExprKind::StructInit => "<struct init>".write(self),
            ExprKind::Assignment { lhs, expr } => (lhs, " = ", expr).write(self),
            ExprKind::Abort { msg } => ("abort(", msg, ")").write(self),
            ExprKind::Unreachable => "unreachable".write(self),
            ExprKind::Break => "break".write(self),
            ExprKind::Continue => "continue".write(self),
            ExprKind::Return(expr) => ("return ", expr).write(self),
            ExprKind::Literal(ref lit) => lit.write(self),
            ExprKind::Binary { lhs, op, rhs } => {
                (inside_expr.then_some("("), lhs, " ", op, " ", rhs, inside_expr.then_some(")"))
                    .write(self);
            }
            ExprKind::OpAssign { place, op, expr } => (place, op, expr).write(self),
            ExprKind::Ident(ident) => ident.write(self),
            ExprKind::Method { ty, method } => (ty, "::", method).write(self),
            ExprKind::FnCall { function, ref args } => {
                (function, "(", Sep(args, ", "), ")").write(self);
            }
            ExprKind::Index { expr, index, .. } => (expr, "[", index, "]").write(self),
            ExprKind::Unary { op, expr } => {
                (inside_expr.then_some("("), op, expr, inside_expr.then_some(")")).write(self);
            }
            ExprKind::Field { expr, field } => (expr, ".", field.to_string().as_str()).write(self),
            ExprKind::Block(ref block) => self.display_block(block),
            ExprKind::FnDecl(ref func) => {
                let FnDecl { ident, for_ty, ref params, ret, ref body } = **func;
                self.inside_expr = inside_expr;
                (
                    "fn ",
                    for_ty.map(|ty| (ty, "::")),
                    ident,
                    params.as_slice(),
                    " -> ",
                    ret,
                    body.as_slice(),
                )
                    .write(self);
            }
            ExprKind::Let { ident, expr } => {
                self.inside_expr = inside_expr;
                let ty = self.hir.exprs[expr].ty;
                ("let ", ident, (": ", ty), " = ").write(self);
                self.inside_expr = false;
                expr.write(self);
            }
            ExprKind::If { ref arms, ref els } => {
                self.inside_expr = inside_expr;
                for (i, arm) in arms.iter().enumerate() {
                    (
                        (i != 0).then_some("else "),
                        "if ",
                        arm.condition,
                        arm.body.as_slice(),
                        (i + 1 != arms.len()).then_some(Line),
                    )
                        .write(self);
                }
                (!els.is_empty()).then_some(("else ", els.as_slice())).write(self);
            }
            ExprKind::ForLoop { ident, iter, ref body } => {
                self.inside_expr = inside_expr;
                ("for ", ident, " in ", iter, body.as_slice()).write(self);
            }
        }
        self.inside_expr = inside_expr;
    }

    fn display_block(&mut self, block: &[ExprId]) {
        if !self.f.chars().next_back().is_some_and(char::is_whitespace) {
            self.f.push(' ');
        }
        self.inside_expr = false;
        if block.is_empty() {
            self.f.push_str("{}");
            return;
        }
        self.indent += 1;
        ("{", Line).write(self);
        for (index, &expr) in block.iter().enumerate() {
            self.inside_expr = false;
            self.display_expr(expr);
            if index + 1 < block.len() {
                self.f.push(';');
            } else {
                self.indent -= 1;
            }
            (Line).write(self);
        }
        self.f.push('}');
    }
}

trait Dump {
    fn write(&self, w: &mut Writer);
}

struct Sep<'a, T, S>(&'a [T], S);

impl<T: Dump, S: Dump> Dump for Sep<'_, T, S> {
    fn write(&self, w: &mut Writer) {
        for (i, arg) in self.0.iter().enumerate() {
            ((i != 0).then_some(&self.1), arg).write(w);
        }
    }
}

impl Dump for [Param<'_>] {
    fn write(&self, w: &mut Writer) {
        ("(", Sep(self, ", "), ")").write(w);
    }
}

impl Dump for Lit {
    fn write(&self, w: &mut Writer) {
        match self {
            Self::Unit => w.f.push_str("()"),
            Self::Bool(bool) => _ = write!(w.f, "{bool}"),
            Self::Int(int) => _ = write!(w.f, "{int}"),
            Self::String(str) => _ = write!(w.f, "{:?}", &**str),
            Self::Char(char) => _ = write!(w.f, "{char:?}"),
            Self::Array { segments } => ("[", Sep(segments, ", "), "]").write(w),
            Self::FStr { segments } => FStr(segments).write(w),
        }
    }
}

struct FStr<'a>(&'a [ExprId]);

impl Dump for FStr<'_> {
    fn write(&self, w: &mut Writer) {
        w.f.push('"');
        for &segment in self.0 {
            let expr = &w.hir.exprs[segment];
            if let ExprKind::Literal(Lit::String(s)) = expr.kind {
                s.write(w);
            } else {
                w.f.push_str("${");
                segment.write(w);
                w.f.push('}');
            }
        }
        w.f.push('"');
    }
}

impl Dump for Param<'_> {
    fn write(&self, w: &mut Writer) {
        (self.ident, ": ", self.ty).write(w);
    }
}

impl Dump for Ty<'_> {
    fn write(&self, w: &mut Writer<'_, '_>) {
        format!("{}", w.tcx.display(*self)).as_str().write(w);
    }
}

impl Dump for ArraySeg {
    fn write(&self, w: &mut Writer) {
        (self.expr, self.repeated.map(|repeated| ("; ", repeated))).write(w);
    }
}

impl Dump for BinaryOp {
    fn write(&self, w: &mut Writer) {
        w.f.push_str(match self {
            Self::And => "and",
            Self::Or => "or",
            Self::Add => "+",
            Self::Div => "/",
            Self::Eq => "==",
            Self::Greater => ">",
            Self::GreaterEq => ">=",
            Self::Less => "<",
            Self::LessEq => "<=",
            Self::Mod => "%",
            Self::Mul => "*",
            Self::Neq => "!=",
            Self::Range => "..",
            Self::RangeInclusive => "..=",
            Self::Sub => "-",
        });
    }
}

impl Dump for OpAssign {
    fn write(&self, w: &mut Writer) {
        (match self {
            Self::Add => "+=",
            Self::Sub => "-=",
            Self::Mul => "*=",
            Self::Div => "/=",
            Self::Mod => "%=",
        })
        .write(w);
    }
}

impl Dump for UnaryOp {
    fn write(&self, w: &mut Writer) {
        w.f.push_str(match self {
            Self::Not => "!",
            Self::Neg => "-",
            Self::Ref => "&",
            Self::Deref => "*",
        });
    }
}

impl Dump for ExprId {
    fn write(&self, w: &mut Writer) {
        w.display_expr(*self);
    }
}

impl Dump for [ExprId] {
    fn write(&self, w: &mut Writer) {
        w.display_block(self);
    }
}

struct Line;
impl Dump for Line {
    fn write(&self, w: &mut Writer) {
        w.f.push('\n');
        w.f.extend(std::iter::repeat_n(' ', w.indent * 4));
    }
}

impl Dump for &'_ str {
    fn write(&self, w: &mut Writer) {
        w.f.push_str(self);
    }
}

impl Dump for Symbol {
    fn write(&self, w: &mut Writer) {
        w.f.push_str(self.as_str());
    }
}

impl<T: Dump> Dump for Option<T> {
    fn write(&self, w: &mut Writer) {
        if let Some(t) = self {
            t.write(w);
        }
    }
}

impl<T: Dump + ?Sized> Dump for &T {
    fn write(&self, w: &mut Writer) {
        T::write(self, w);
    }
}

macro_rules! impl_tuples {
    ($($t:ident),+) => {
        impl<$($t: Dump),+> Dump for ($($t),+,) {
            fn write(&self, w: &mut Writer) {
                #[allow(non_snake_case)]
                let ($($t),+,) = self;
                $($t.write(w));+
            }
        }
    };
}

impl_tuples!(A);
impl_tuples!(A, B);
impl_tuples!(A, B, C);
impl_tuples!(A, B, C, D);
impl_tuples!(A, B, C, D, E);
impl_tuples!(A, B, C, D, E, F);
impl_tuples!(A, B, C, D, E, F, G);
