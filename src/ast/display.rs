use std::{
    fmt::{self, Write},
    mem,
};

use crate::ast::{Ast, BinaryOp, BlockId, Expr, ExprId, Lit, Ty, UnaryOp};

use super::TypeId;
struct Writer<'ast> {
    ast: &'ast Ast,
    f: String,
    indent: usize,
    inside_expr: bool,
}

impl fmt::Display for Ast {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let f = String::new();
        let mut writer = Writer { ast: self, f, indent: 0, inside_expr: false };
        for &expr in &self.top_level {
            writer.display_expr(expr);
            writer.ln();
        }
        #[cfg(debug_assertions)]
        crate::parse::parse(&writer.f).unwrap();
        fmt.write_str(&writer.f)
    }
}

impl Writer<'_> {
    fn display_ty(&mut self, ty: TypeId) {
        let ty = &self.ast.types[ty];
        match ty {
            Ty::Never => self.f.push('!'),
            Ty::Unit => self.f.push_str("()"),
            Ty::Array(ty) => {
                self.f.push('[');
                self.display_ty(*ty);
                self.f.push(']');
            }
            Ty::Name(name) => self.f.push_str(name),
        }
    }
    #[expect(clippy::too_many_lines)]
    fn display_expr(&mut self, expr: ExprId) {
        // FIXME: take precedence into account to use minimum parens needed
        let inside_expr = mem::replace(&mut self.inside_expr, true);
        match &self.ast.exprs[expr] {
            Expr::Break => self.f.push_str("break"),
            Expr::Return(expr) => {
                self.f.push_str("return");
                if let Some(expr) = expr {
                    self.f.push(' ');
                    self.display_expr(*expr);
                }
            }
            Expr::Lit(lit) => self.display_lit(lit),
            Expr::Binary { lhs, op, rhs } => {
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
            Expr::Ident(ident) => self.f.push_str(ident),
            Expr::FnCall { function, args } => {
                self.display_expr(*function);
                self.f.push('(');
                for (i, arg) in args.iter().enumerate() {
                    self.f.push_str(if i == 0 { "" } else { ", " });
                    self.display_expr(*arg);
                }
                self.f.push(')');
            }
            Expr::Index { expr, index } => {
                self.display_expr(*expr);
                self.f.push('[');
                self.display_expr(*index);
                self.f.push(']');
            }
            Expr::Unary { op, expr } => {
                if inside_expr {
                    self.f.push('(');
                }
                self.display_unary_op(*op);
                self.display_expr(*expr);
                if inside_expr {
                    self.f.push(')');
                }
            }
            Expr::MethodCall { expr, method, args } => {
                self.display_expr(*expr);
                self.f.push('.');
                self.f.push_str(method);
                self.f.push('(');
                for (i, arg) in args.iter().enumerate() {
                    self.f.push_str(if i == 0 { "" } else { ", " });
                    self.display_expr(*arg);
                }
                self.f.push(')');
            }
            Expr::FieldAccess { expr, field } => {
                // NOTE: FieldAccess should always be higher priority, so we shouldn't need to wrap with parens
                self.display_expr(*expr);
                self.f.push('.');
                self.f.push_str(field);
            }
            Expr::StructInit { ident, args } => {
                self.f.push_str(ident);
                self.f.push_str(" {");
                for (i, arg) in args.iter().enumerate() {
                    self.f.push_str(if i == 0 { "" } else { ", " });
                    self.f.push_str(&arg.field);
                    if let Some(expr) = arg.expr {
                        self.f.push_str(": ");
                        self.display_expr(expr);
                    }
                }
                self.f.push('}');
            }
            Expr::Block(block) => self.display_block(*block),
            Expr::FnDecl { ident, params, ret, block } => {
                self.inside_expr = inside_expr;
                _ = write!(self.f, "fn {ident}(");

                for (i, param) in params.iter().enumerate() {
                    self.f.push_str(if i == 0 { "" } else { ", " });
                    self.f.push_str(&param.ident);
                    self.f.push_str(": ");
                    self.display_ty(param.ty);
                }
                self.f.push(')');

                if let Some(ret) = ret {
                    self.f.push_str(" -> ");
                    self.display_ty(*ret);
                }

                self.display_block(*block);
            }
            Expr::Let { ident, ty, expr } => {
                self.inside_expr = inside_expr;
                self.f.push_str("let ");
                self.f.push_str(ident);
                if let Some(ty) = ty {
                    self.f.push_str(": ");
                    self.display_ty(*ty);
                }
                self.f.push_str(" = ");

                self.inside_expr = false;
                self.display_expr(*expr);
            }
            Expr::While { condition, block } => {
                self.inside_expr = inside_expr;
                self.f.push_str("while ");
                self.display_expr(*condition);
                self.display_block(*block);
            }
            Expr::If { arms, els } => {
                self.inside_expr = inside_expr;
                for (i, arm) in arms.iter().enumerate() {
                    if i != 0 {
                        self.f.push_str("else ");
                    }
                    self.f.push_str("if ");
                    self.display_expr(arm.condition);
                    self.display_block(arm.body);
                    if i + 1 != arms.len() {
                        self.ln();
                    }
                }
                if let &Some(els) = els {
                    self.f.push_str("else ");
                    self.display_block(els);
                }
            }
        }
        self.inside_expr = inside_expr;
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
            B::AddAssign => "+=",
            B::Div => "/",
            B::DivAssign => "/=",
            B::Eq => "==",
            B::Greater => ">",
            B::GreaterEq => ">=",
            B::Less => "<",
            B::LessEq => "<=",
            B::Mod => "%",
            B::ModAssign => "%=",
            B::Mul => "*",
            B::MulAssign => "*=",
            B::Neq => "!=",
            B::Range => "..",
            B::RangeInclusive => "..=",
            B::Sub => "-",
            B::SubAssign => "-=",
            B::Assign => "=",
        };
        self.f.push_str(str);
    }

    fn display_lit(&mut self, lit: &Lit) {
        match lit {
            Lit::Abort => self.f.push_str("abort"),
            Lit::Unit => self.f.push_str("()"),
            Lit::Bool(bool) => _ = write!(self.f, "{bool}"),
            Lit::Int(int) => _ = write!(self.f, "{int}"),
            Lit::Str(str) => _ = write!(self.f, "{:?}", &**str),
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
        self.f.push('{');
        self.ln();
        for (index, &expr) in block.stmts.iter().enumerate() {
            self.inside_expr = false;
            self.display_expr(expr);
            if !block.is_expr || index + 1 < block.stmts.len() {
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
