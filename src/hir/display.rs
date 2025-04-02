use std::{
    fmt::{self, Write},
    mem,
};

use super::{ExprKind, FnDecl, LValue, Param};
use crate::{
    hir::{BinaryOp, ExprId, Hir, Lit, Ty, UnaryOp},
    ty::TyKind,
};

struct Writer<'hir, 'tcx> {
    hir: &'hir Hir<'tcx>,
    f: String,
    indent: usize,
    inside_expr: bool,
}

impl fmt::Display for Hir<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let f = String::new();
        let mut writer = Writer { hir: self, f, indent: 0, inside_expr: false };
        for &expr in &self.root {
            writer.display_expr(expr);
            writer.ln();
        }
        fmt.write_str(&writer.f)
    }
}

impl Writer<'_, '_> {
    fn display_ty(&mut self, ty: Ty) {
        // FIXME: we'll need tcx to read the names of structs/generics, etc..
        let str = match *ty {
            TyKind::Never => "!",
            TyKind::Unit => "()",
            TyKind::Bool => "bool",
            TyKind::Int => "int",
            TyKind::Char => "char",
            TyKind::Str => "str",
            TyKind::Infer(..) => panic!(),
            TyKind::Array(of) => {
                self.f.push('[');
                self.display_ty(of);
                self.f.push(']');
                return;
            }
            TyKind::Generic(..) => "<generic>",
            TyKind::Range => "<range>",
            TyKind::RangeInclusive => "<range_inclusive>",
            TyKind::Struct { .. } | TyKind::Function { .. } => "<unnamable>",
        };
        self.f.push_str(str);
    }
    #[allow(clippy::too_many_lines)]
    fn display_expr(&mut self, expr: ExprId) {
        // FIXME: take precedence into account to use minimum parens needed
        let inside_expr = mem::replace(&mut self.inside_expr, true);
        match &self.hir.exprs[expr].kind {
            ExprKind::Unreachable => self.f.push_str("unreachable"),
            ExprKind::Abort => self.f.push_str("abort"),
            &ExprKind::Field { expr, field } => {
                self.display_expr(expr);
                _ = write!(self.f, ".{field}");
            }
            ExprKind::StructInit => self.f.push_str("<struct init>"),
            ExprKind::PrintStr(s) => {
                self.f.push_str("print ");
                _ = write!(self.f, "{s:?}");
            }
            ExprKind::Return(expr) => {
                self.f.push_str("return");
                self.display_expr(*expr);
            }
            ExprKind::Break => self.f.push_str("break"),
            ExprKind::Literal(lit) => self.display_lit(lit),
            ExprKind::Binary { lhs, op, rhs } => {
                if inside_expr {
                    self.f.push('(');
                }
                self.display_expr(*lhs);
                self.f.push(' ');
                self.display_binary_op(*op);
                self.f.push(' ');
                self.display_expr(*rhs);
                if inside_expr {
                    self.f.push(')');
                }
            }
            ExprKind::Assignment { lhs, expr } => {
                self.display_lvalue(lhs);
                self.f.push_str(" = ");
                self.display_expr(*expr);
            }
            ExprKind::Ident(ident) => self.f.push_str(ident),
            ExprKind::FnCall { function, args } => {
                self.display_expr(*function);
                self.f.push('(');
                for (i, arg) in args.iter().enumerate() {
                    self.f.push_str(if i == 0 { "" } else { ", " });
                    self.display_expr(*arg);
                }
                self.f.push(')');
            }
            ExprKind::Index { expr, index } => {
                self.display_expr(*expr);
                self.f.push('[');
                self.display_expr(*index);
                self.f.push(']');
            }
            ExprKind::Unary { op, expr } => {
                if inside_expr {
                    self.f.push('(');
                }
                self.display_unary_op(*op);
                self.display_expr(*expr);
                if inside_expr {
                    self.f.push(')');
                }
            }
            ExprKind::Block(block) => self.display_block(block),
            ExprKind::FnDecl(decl) => {
                let FnDecl { ident, params, ret, body } = &**decl;
                self.inside_expr = inside_expr;
                _ = write!(self.f, "fn {ident}(");
                self.display_params(params);
                self.f.push_str(") -> ");
                self.display_ty(ret);
                self.display_block(body);
            }
            ExprKind::Let { ident, expr } => {
                self.inside_expr = inside_expr;
                _ = write!(self.f, "let {ident}: ");
                self.display_ty(self.hir.exprs[*expr].ty);
                self.f.push_str(" = ");

                self.inside_expr = false;
                self.display_expr(*expr);
            }
            ExprKind::Loop(block) => {
                self.f.push_str("loop");
                self.display_block(block);
            }
            ExprKind::If { arms, els } => {
                self.inside_expr = inside_expr;
                for (i, arm) in arms.iter().enumerate() {
                    if i != 0 {
                        self.f.push_str("else ");
                    }
                    self.f.push_str("if ");
                    self.display_expr(arm.condition);
                    self.display_block(&arm.body);
                    self.ln();
                }
                if !els.is_empty() {
                    self.f.push_str("else ");
                    self.display_block(els);
                }
            }
        }
        self.inside_expr = inside_expr;
    }
    fn display_params(&mut self, params: &[Param]) {
        for (i, param) in params.iter().enumerate() {
            self.f.push_str(if i == 0 { "" } else { ", " });
            self.f.push_str(&param.ident);
            self.f.push_str(": ");
            self.display_ty(param.ty);
        }
    }

    fn display_lvalue(&mut self, lvalue: &LValue) {
        match lvalue {
            LValue::Name(name) => self.f.push_str(name),
            LValue::Field { expr, field } => {
                self.display_lvalue(expr);
                _ = write!(self.f, ".{field}");
            }
            LValue::Index { indexee, index } => {
                self.display_lvalue(indexee);
                self.f.push('[');
                self.display_expr(*index);
                self.f.push(']');
            }
        }
    }

    fn display_unary_op(&mut self, op: UnaryOp) {
        let str = match op {
            UnaryOp::Not => "!",
            UnaryOp::Neg => "-",
        };
        self.f.push_str(str);
    }

    fn display_binary_op(&mut self, op: BinaryOp) {
        use BinaryOp as B;
        let str = match op {
            B::Add => "+",
            B::Sub => "-",
            B::Mul => "*",
            B::Div => "/",
            B::Mod => "%",

            B::Range => "..",
            B::RangeInclusive => "..=",

            B::Eq => "==",
            B::Greater => ">",
            B::GreaterEq => ">=",
            B::Less => "<",
            B::LessEq => "<=",
            B::Neq => "!=",
        };
        self.f.push_str(str);
    }

    fn display_lit(&mut self, lit: &Lit) {
        match lit {
            Lit::Unit => self.f.push_str("()"),
            Lit::Bool(bool) => _ = write!(self.f, "{bool}"),
            Lit::Int(int) => _ = write!(self.f, "{int}"),
            Lit::String(str) => _ = write!(self.f, "{:?}", &**str),
            Lit::Char(char) => _ = write!(self.f, "{char:?}"),
            Lit::Array { segments } => {
                self.f.push('[');
                for (i, segment) in segments.iter().enumerate() {
                    self.f.push_str(if i == 0 { "" } else { ", " });
                    self.display_expr(segment.expr);
                    if let Some(repeated) = segment.repeated {
                        self.f.push_str("; ");
                        self.display_expr(repeated);
                    }
                }
                self.f.push(']');
            }
        }
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
        self.f.push('{');
        self.ln();
        for (index, &expr) in block.iter().enumerate() {
            self.inside_expr = false;
            self.display_expr(expr);
            if index + 1 < block.len() {
                self.f.push(';');
            }
            self.ln();
        }
        self.indent -= 1;
        for _ in 0..4 {
            self.f.pop().unwrap();
        }
        self.f.push('}');
    }

    fn ln(&mut self) {
        self.f.push('\n');
        self.f.extend(std::iter::repeat_n(' ', self.indent * 4));
    }
}
