use std::{
    fmt::{self, Write},
    mem,
};

use thin_vec::ThinVec;

use super::{
    ArraySeg, ExprKind, Field, FnDecl, Ident, MatchArm, Param, Pat, PatArg, PatKind, Trait, TyKind,
    TypeId,
};
use crate::{
    ast::{
        Ast, BinaryOp, BlockId, ExprId, Inclusive, ItemId, ItemKind, Lit, Path, Stmt, UnaryOp, Use,
        UseKind,
    },
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
        self.root.items.iter().for_each(|item| (item, Line).write(&mut w));
        fmt.write_str(&w.f)
    }
}

impl Dump for ItemId {
    fn write(&self, w: &mut Writer) {
        match &w.ast.items[*self].kind {
            ItemKind::Struct(ident, generics, fields) => {
                ("struct ", ident, Generics(generics), fields).write(w);
            }
            ItemKind::Const(ident, ty, expr) => {
                ("const ", ident, ty.map(|ty| (": ", ty)), " = ").write(w);
                expr.write(w);
            }
            ItemKind::FnDecl(decl) => decl.write(w),
            ItemKind::Trait(Trait { ident, methods }) => {
                ("trait ", ident, methods).write(w);
            }
            ItemKind::Module(ident, module) => {
                ("mod ", ident, LBrace, Sep(&module.items, Line), RBrace).write(w);
            }
            ItemKind::Use(use_) => ("use ", &use_.path, &use_.kind, ";").write(w),
            ItemKind::Impl(impl_) => {
                (
                    "impl",
                    Generics(&impl_.generics),
                    " ",
                    impl_.ty,
                    Braced(Sep(&impl_.methods, Line)),
                )
                    .write(w);
            }
        }
    }
}

impl Writer<'_> {
    fn display_expr(&mut self, expr: ExprId) {
        let inside_expr = mem::replace(&mut self.inside_expr, true);
        match self.ast.exprs[expr].kind {
            ExprKind::Match { scrutinee, ref arms } => {
                ("match ", scrutinee, " {").write(self);
                self.indent += 1;
                (Line, Sep(arms, (",", Line))).write(self);
                self.indent -= 1;
                (Line, "}").write(self);
            }
            ExprKind::Is { scrutinee, ref pat } => {
                (inside_expr.then_some("("), scrutinee, " is ", pat, inside_expr.then_some(")"))
                    .write(self);
            }
            ExprKind::Unreachable => "unreachable".write(self),
            ExprKind::Assert(expr) => ("assert ", expr).write(self),
            ExprKind::Break => "break".write(self),
            ExprKind::Continue => "continue".write(self),
            ExprKind::Return(expr) => ("return", expr.map(|expr| (" ", expr))).write(self),
            ExprKind::Lit(ref lit) => lit.write(self),
            ExprKind::Binary { lhs, op, rhs } => {
                (inside_expr.then_some("("), lhs, " ", op, " ", rhs, inside_expr.then_some(")"))
                    .write(self);
            }
            ExprKind::Path(ref path) => path.write(self),
            ExprKind::FnCall { function, ref args } => {
                (function, "(", Sep(args, ", "), ")").write(self);
            }
            ExprKind::Index { expr, index } => (expr, "[", index, "]").write(self),
            ExprKind::Unary { op, expr } => {
                (inside_expr.then_some("("), op, expr, inside_expr.then_some(")")).write(self);
            }
            ExprKind::MethodCall { expr, method, ref args, .. } => {
                (expr, ".", method, "(", Sep(args, ", "), ")").write(self);
            }
            ExprKind::FieldAccess { expr, field, .. } => (expr, ".", field).write(self),
            ExprKind::Block(block) => self.display_block(block),
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
                    ((i != 0).then_some(" else "), "if ", arm.condition, arm.body).write(self);
                }
                els.map(|els| (" else ", els)).write(self);
            }
        }
    }

    fn display_block(&mut self, block: BlockId) {
        let block = &self.ast.blocks[block];
        if !self.f.chars().next_back().is_some_and(char::is_whitespace) {
            self.f.push(' ');
        }
        self.inside_expr = false;
        if block.expr.is_none() && block.stmts.is_empty() {
            self.f.push_str("{}");
            return;
        }
        self.indent += 1;
        ("{", (!block.stmts.is_empty() || block.expr.is_some()).then_some(Line)).write(self);
        for (i, stmt) in block.stmts.iter().enumerate() {
            self.inside_expr = false;
            (stmt, ";", (i + 1 != block.stmts.len() || block.expr.is_some()).then_some(Line))
                .write(self);
        }
        if let Some(expr) = &block.expr {
            expr.write(self);
        }
        RBrace.write(self);
    }
}
trait Dump {
    fn write(&self, w: &mut Writer);
}

impl Dump for Stmt {
    fn write(&self, w: &mut Writer) {
        match self {
            Self::Expr(expr) => expr.write(w),
            Self::Item(item) => item.write(w),
        }
    }
}

struct Sep<'a, T, S>(&'a [T], S);

impl<T: Dump, S: Dump> Dump for Sep<'_, T, S> {
    fn write(&self, w: &mut Writer) {
        for (i, arg) in self.0.iter().enumerate() {
            ((i != 0).then_some(&self.1), arg).write(w);
        }
    }
}

impl Dump for Pat {
    fn write(&self, w: &mut Writer) {
        self.kind.write(w);
    }
}

impl Dump for PatKind {
    fn write(&self, w: &mut Writer) {
        match *self {
            Self::RangeFull => Inclusive::No.write(w),
            Self::Range(ref pats, inclusive) => (&pats[0], inclusive, &pats[1]).write(w),
            Self::Bool(bool) => Lit::Bool(bool).write(w),
            Self::Ident(ident) => ident.write(w),
            Self::Struct(ident, ref fields) => (ident, "(", Sep(fields, ", "), ")").write(w),
            Self::Str(str) => Lit::Str(str).write(w),
            Self::Int(int) => Lit::Int(int).write(w),
            Self::Expr(block) => block.write(w),
            Self::If(expr) => ("if ", expr).write(w),
            Self::Or(ref pats) => Sep(pats, " or ").write(w),
            Self::And(ref pats) => Sep(pats, " and ").write(w),
            Self::Array(ref pats) => ("[", Sep(pats, ", "), "]").write(w),
        }
    }
}

impl Dump for Inclusive {
    fn write(&self, w: &mut Writer) {
        match self {
            Self::Yes => "..=",
            Self::No => "..",
        }
        .write(w);
    }
}

impl Dump for PatArg {
    fn write(&self, w: &mut Writer) {
        (self.ident, ": ", &self.pat).write(w);
    }
}

impl Dump for MatchArm {
    fn write(&self, w: &mut Writer) {
        (&self.pat, " => ", self.body).write(w);
    }
}

impl Dump for ThinVec<Param> {
    fn write(&self, w: &mut Writer) {
        ("(", Sep(self, ", "), ")").write(w);
    }
}

impl Dump for ThinVec<Field> {
    fn write(&self, w: &mut Writer) {
        ("(", Sep(self, ", "), ")").write(w);
    }
}

struct Generics<'a>(&'a ThinVec<Ident>);

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
                let str = str.replace('\n', "\\n");
                w.f.push_str(&str);
            } else {
                w.f.push_str("${");
                seg.write(w);
                w.f.push('}');
            }
        }
        w.f.push('"');
    }
}

impl Dump for Use {
    fn write(&self, w: &mut Writer) {
        (&self.path, &self.kind).write(w);
    }
}

impl Dump for UseKind {
    fn write(&self, w: &mut Writer) {
        "::".write(w);
        match self {
            Self::Wildcard => "*".write(w),
            Self::Block(imports) => Braced(Sep(imports, ", ")).write(w),
        }
    }
}

impl Dump for FnDecl {
    fn write(&self, w: &mut Writer) {
        let current = w.inside_expr;
        let Self { ident, ref generics, ref params, ret, block, .. } = *self;
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

impl Dump for ThinVec<ExprId> {
    fn write(&self, w: &mut Writer) {
        w.f.push(' ');
        w.inside_expr = false;
        if self.is_empty() {
            w.f.push_str("{}");
            return;
        }
        LBrace.write(w);
        for (index, decl) in self.iter().enumerate() {
            decl.write(w);
            if index + 1 == self.len() {
                (Line).write(w);
            }
        }
        RBrace.write(w);
        w.f.push('}');
    }
}

impl Dump for Param {
    fn write(&self, w: &mut Writer) {
        (self.ident, self.ty.map(|ty| (": ", ty))).write(w);
    }
}

impl Dump for Field {
    fn write(&self, w: &mut Writer) {
        (self.ident, ": ", self.ty).write(w);
    }
}

impl Dump for Ident {
    fn write(&self, w: &mut Writer) {
        self.symbol.write(w);
    }
}

impl Dump for TypeId {
    fn write(&self, w: &mut Writer) {
        match &w.ast.types[*self].kind {
            TyKind::Ref(inner) => ("&", inner).write(w),
            TyKind::Func { params, ret } => {
                ("fn(", Sep(params, ", "), ")", ret.map(|ret| (" -> ", ret))).write(w);
            }
            TyKind::Never => w.f.push('!'),
            TyKind::Unit => w.f.push_str("()"),
            TyKind::Array(of) => ("[", of, "]").write(w),
            TyKind::Name { path, generics } if generics.is_empty() => path.write(w),
            TyKind::Name { path, generics } => (path, "<", Sep(generics, ", "), ">").write(w),
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

impl Dump for Path {
    fn write(&self, w: &mut Writer) {
        Sep(&self.segments, "::").write(w);
    }
}

struct Line;
struct LBrace;
struct RBrace;

impl Dump for Line {
    fn write(&self, w: &mut Writer) {
        w.f.push('\n');
        w.f.extend(std::iter::repeat_n(' ', w.indent * 4));
    }
}

impl Dump for LBrace {
    fn write(&self, w: &mut Writer) {
        w.indent += 1;
        (" {", Line).write(w);
    }
}

impl Dump for RBrace {
    fn write(&self, w: &mut Writer) {
        w.indent -= 1;
        (Line, "}").write(w);
    }
}

struct Braced<T>(T);

impl<T: Dump> Dump for Braced<T> {
    fn write(&self, w: &mut Writer) {
        (LBrace, &self.0, RBrace).write(w);
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
