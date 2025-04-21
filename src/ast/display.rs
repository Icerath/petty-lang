use std::{
    fmt::{self, Write},
    mem,
};

use thin_vec::ThinVec;

use super::{ArraySeg, ExprKind, FnDecl, Impl, Param, Trait, TyKind, TypeId};
use crate::{
    ast::{Ast, BinaryOp, BlockId, ExprId, Lit, UnaryOp},
    symbol::Symbol,
};

struct Writer<'ast> {
    ast: &'ast Ast,
    f: String,
    indent: usize,
    inside_expr: bool,
}

impl fmt::Display for Ast {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let f = String::new();
        let mut w = Writer { ast: self, f, indent: 0, inside_expr: false };
        self.top_level.iter().for_each(|expr| (expr, Line).write(&mut w));
        #[cfg(debug_assertions)]
        crate::parse::parse(&w.f, None).unwrap();
        fmt.write_str(&w.f)
    }
}

impl Writer<'_> {
    fn display_expr(&mut self, expr: ExprId) {
        let inside_expr = mem::replace(&mut self.inside_expr, true);
        match self.ast.exprs[expr].kind {
            ExprKind::Impl(Impl { trait_, ty, ref methods }) => {
                ("impl ", trait_, " for ", ty, methods).write(self);
            }
            ExprKind::Unreachable => "unreachable".write(self),
            ExprKind::Assert(expr) => ("assert ", expr).write(self),
            ExprKind::Struct { ident, ref fields, .. } => ("struct ", ident, fields).write(self),
            ExprKind::Break => "break".write(self),
            ExprKind::Continue => "continue".write(self),
            ExprKind::Return(expr) => ("return", expr.map(|expr| (" ", expr))).write(self),
            ExprKind::Lit(ref lit) => lit.write(self),
            ExprKind::Binary { lhs, op, rhs } => {
                (inside_expr.then_some("("), lhs, " ", op, " ", rhs, inside_expr.then_some(")"))
                    .write(self);
            }
            ExprKind::Ident(ident) => ident.write(self),
            ExprKind::FnCall { function, ref args } => {
                (function, "(", Sep(args, ", "), ")").write(self);
            }
            ExprKind::Index { expr, index } => (expr, "[", index, "]").write(self),
            ExprKind::Unary { op, expr } => {
                (inside_expr.then_some("("), op, expr, inside_expr.then_some(")")).write(self);
            }
            ExprKind::MethodCall { expr, method, ref args } => {
                (expr, ".", method, "(", Sep(args, ", "), ")").write(self);
            }
            ExprKind::FieldAccess { expr, field, .. } => (expr, ".", field).write(self),
            ExprKind::Block(block) => self.display_block(block),
            ExprKind::FnDecl(ref decl) => decl.write(self),
            ExprKind::Trait(Trait { ident, ref methods }) => {
                ("trait ", ident, methods).write(self);
            }
            ExprKind::Let { ident, ty, expr } => {
                self.inside_expr = inside_expr;
                ("let ", ident, ty.map(|ty| (": ", ty)), " = ").write(self);
                self.inside_expr = false;
                expr.write(self);
            }
            ExprKind::For { ident, iter, body } => {
                ("for ", ident, " in ", iter, body).write(self);
            }
            ExprKind::While { condition, block } => {
                self.inside_expr = inside_expr;
                ("while ", condition, block).write(self);
            }
            ExprKind::If { ref arms, els } => {
                self.inside_expr = inside_expr;
                for (i, arm) in arms.iter().enumerate() {
                    (
                        (i != 0).then_some("else "),
                        "if ",
                        arm.condition,
                        arm.body,
                        (i + 1 != arms.len()).then_some(Line),
                    )
                        .write(self);
                }
                els.map(|els| ("else ", els)).write(self);
            }
        }
    }

    fn display_block(&mut self, block: BlockId) {
        let block = &self.ast.blocks[block];
        if !self.f.chars().next_back().is_some_and(char::is_whitespace) {
            self.f.push(' ');
        }
        self.inside_expr = false;
        if block.stmts.is_empty() {
            self.f.push_str("{}");
            return;
        }
        self.indent += 1;
        ("{", Line).write(self);
        for (index, &expr) in block.stmts.iter().enumerate() {
            self.inside_expr = false;
            self.display_expr(expr);
            if !block.is_expr || index + 1 < block.stmts.len() {
                self.f.push(';');
            }
            if index + 1 == block.stmts.len() {
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

impl Dump for ThinVec<Param> {
    fn write(&self, w: &mut Writer) {
        ("(", Sep(self, ", "), ")").write(w);
    }
}

struct Generics<'a>(&'a ThinVec<Symbol>);

impl Dump for Generics<'_> {
    fn write(&self, w: &mut Writer) {
        (!self.0.is_empty()).then_some(("<", Sep(self.0, ", "), ">")).write(w);
    }
}

impl Dump for Lit {
    fn write(&self, w: &mut Writer) {
        match self {
            Self::Unit => w.f.push_str("()"),
            Self::Bool(bool) => _ = write!(w.f, "{bool}"),
            Self::Int(int) => _ = write!(w.f, "{int}"),
            Self::Str(str) => _ = write!(w.f, "{:?}", &**str),
            Self::FStr(segments) => FStr(segments).write(w),
            Self::Char(char) => _ = write!(w.f, "{char:?}"),
            Self::Array { segments } => ("[", Sep(segments, ", "), "]").write(w),
        }
    }
}

struct FStr<'a>(&'a [ExprId]);

impl Dump for FStr<'_> {
    fn write(&self, w: &mut Writer) {
        w.f.push('"');
        for &seg in self.0 {
            let expr = &w.ast.exprs[seg];
            if let ExprKind::Lit(Lit::Str(str)) = &expr.kind {
                w.f.push_str(str);
            } else {
                w.f.push_str("${");
                seg.write(w);
                w.f.push('}');
            }
        }
        w.f.push('"');
    }
}

impl Dump for FnDecl {
    fn write(&self, w: &mut Writer) {
        let current = w.inside_expr;
        let Self { ident, ref generics, ref params, ret, block } = *self;
        ("fn ", ident, Generics(generics), params, ret.map(|ret| (" -> ", ret))).write(w);
        match block {
            Some(block) => block.write(w),
            None => ";".write(w),
        }
        w.inside_expr = current;
    }
}

impl Dump for ThinVec<FnDecl> {
    fn write(&self, w: &mut Writer) {
        w.f.push(' ');
        w.inside_expr = false;
        if self.is_empty() {
            w.f.push_str("{}");
            return;
        }
        w.indent += 1;
        ("{", Line).write(w);
        for (index, decl) in self.iter().enumerate() {
            decl.write(w);
            if index + 1 == self.len() {
                w.indent -= 1;
            }
            (Line).write(w);
        }
        w.f.push('}');
    }
}

impl Dump for Param {
    fn write(&self, w: &mut Writer) {
        (self.ident, ": ", self.ty).write(w);
    }
}

impl Dump for TypeId {
    fn write(&self, w: &mut Writer) {
        match w.ast.types[*self].kind {
            TyKind::Ref(inner) => ("&", inner).write(w),
            TyKind::Func { ref params, ret } => {
                ("fn(", Sep(params, ", "), ")", ret.map(|ret| (" -> ", ret))).write(w);
            }
            TyKind::Never => w.f.push('!'),
            TyKind::Unit => w.f.push_str("()"),
            TyKind::Array(of) => ("[", of, "]").write(w),
            TyKind::Name(name) => w.f.push_str(&name),
        }
    }
}

impl Dump for ArraySeg {
    fn write(&self, w: &mut Writer) {
        (self.expr, self.repeated.map(|repeated| ("; ", repeated))).write(w);
    }
}

impl Dump for BinaryOp {
    fn write(&self, w: &mut Writer) {
        w.f.push_str(self.kind.symbol());
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

impl Dump for BlockId {
    fn write(&self, w: &mut Writer) {
        w.display_block(*self);
    }
}

struct Line;
impl Dump for Line {
    fn write(&self, w: &mut Writer) {
        w.f.push('\n');
        w.f.extend(std::iter::repeat_n(' ', w.indent * 4));
    }
}

impl Dump for &'static str {
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
