use crate::crel::ast::*;
use std::collections::HashMap;

pub struct CRelInliner {
  replacements: HashMap<String, Expression>,
}

impl CRelInliner {

  pub fn new() -> Self {
    CRelInliner {
      replacements: HashMap::new(),
    }
  }

  pub fn inline_crel(&mut self, crel: &CRel) -> CRel {
    match crel {
      CRel::Declaration(decl) => {
        self.add_declaration(decl);
        CRel::Seq(Vec::new())
      },
      CRel::FunctionDefinition{ specifiers, name, params, body } => {
        CRel::FunctionDefinition {
          specifiers: specifiers.clone(),
          name: name.clone(),
          params: params.clone(),
          body: Box::new(self.inline_statement(body)),
        }
      },
      CRel::Seq(crels) => {
        CRel::Seq(crels.into_iter()
                  .map(|crel| self.inline_crel(crel))
                  .filter(|crel| match crel {
                    CRel::Seq(vec) if vec.is_empty() => false,
                    _ => true,
                  })
                  .collect())
      }
    }
  }

  pub fn inline_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::Assert(expr) => {
        Statement::Assert(Box::new(self.inline_expression(expr)))
      },
      Statement::Assume(expr) => {
        Statement::Assume(Box::new(self.inline_expression(expr)))
      },
      Statement::BasicBlock(items) => {
        Statement::BasicBlock(items.into_iter()
                              .map(|item| self.inline_block_item(item))
                              .filter(|item| match item {
                                BlockItem::Statement(stmt) if stmt.is_none() => false,
                                _ => true,
                              }).collect())
      },
      Statement::Break => Statement::Break,
      Statement::Compound(items) => {
        Statement::Compound(items.into_iter()
                            .map(|item| self.inline_block_item(item))
                            .filter(|item| match item {
                              BlockItem::Statement(stmt) if stmt.is_none() => false,
                              _ => true,
                            }).collect())

      },
      Statement::Expression(expr) => {
        Statement::Expression(Box::new(self.inline_expression(expr)))
      },
      Statement::GuardedRepeat { id, repetitions, condition, body } => {
        let orig_replacements = self.replacements.clone();
        let new_body = self.inline_statement(body);
        self.replacements = orig_replacements;
        Statement::GuardedRepeat {
          id: id.clone(),
          repetitions: repetitions.clone(),
          condition: Box::new(self.inline_expression(condition)),
          body: Box::new(new_body),
        }
      },
      Statement::If{ condition, then, els } => {
        let orig_replacements = self.replacements.clone();
        let _new_then = self.inline_statement(then);
        let mut added_in_then = self.replacements.clone();
        added_in_then.retain(|k,v| orig_replacements.get(k) != Some(v));
        self.replacements = orig_replacements.clone();

        let _new_els = els.as_ref().map(|els| Box::new(self.inline_statement(&els)));
        let mut added_in_els = self.replacements.clone();
        added_in_els.retain(|k,v| orig_replacements.get(k) != Some(v));
        self.replacements = orig_replacements.clone();

        for (var_name, then_val) in &added_in_then {
          let els_val = match added_in_els.get(var_name) {
            None => orig_replacements.get(var_name).unwrap_or(&Expression::ConstInt(0)),
            Some(val) => val,
          };
          self.replacements.insert(var_name.clone(), Expression::Ternary {
            condition: condition.clone(),
            then: Box::new(then_val.clone()),
            els: Box::new(els_val.clone()),
          });
        }
        for (var_name, els_val) in &added_in_els {
          if added_in_then.contains_key(var_name) { continue; }
          let then_val = orig_replacements.get(var_name).unwrap_or(&Expression::ConstInt(0));
          self.replacements.insert(var_name.clone(), Expression::Ternary {
            condition: condition.clone(),
            then: Box::new(then_val.clone()),
            els: Box::new(els_val.clone()),
          });
        };
        Statement::None
      },
      Statement::None => Statement::None,
      Statement::Relation{ lhs, rhs } => Statement::Relation {
        lhs: Box::new(self.inline_statement(lhs)),
        rhs: Box::new(self.inline_statement(rhs)),
      },
      Statement::Return(expr) => match expr {
        None => Statement::None,
        Some(expr) => {
          let mut curr = self.inline_expression(&expr);
          let mut next = self.inline_expression(&curr);
          let mut fuel = 20;
          while fuel > 0 && curr != next {
            curr = next;
            next = self.inline_expression(&curr);
            fuel -= 1;
          }
          Statement::Expression(Box::new(curr))
        }
      },
      Statement::While{..} => panic!("Can't inline over while"),
    }
  }

  pub fn inline_expression(&mut self, expr: &Expression) -> Expression {
    match expr {
      Expression::Identifier { name } => {
        match self.replacements.get(name) {
          None => expr.clone(),
          Some(rep) => rep.clone(),
        }
      },
      Expression::ConstInt(_) => expr.clone(),
      Expression::ConstBool(_) => expr.clone(),
      Expression::ConstFloat(_) => expr.clone(),
      Expression::StringLiteral(_) => expr.clone(),
      Expression::Ternary { condition, then, els } => Expression::Ternary {
        condition: Box::new(self.inline_expression(condition)),
        then: Box::new(self.inline_expression(then)),
        els: Box::new(self.inline_expression(els)),
      },
      Expression::Call{ callee, args } => Expression::Call {
        callee: Box::new(self.inline_expression(callee)),
        args: args.into_iter().map(|arg| self.inline_expression(arg)).collect(),
      },
      Expression::Unop{ expr, op } => Expression::Unop {
        expr: Box::new(self.inline_expression(expr)),
        op: op.clone(),
      },
      Expression::Binop{ lhs, rhs, op } if *op == BinaryOp::Assign => {
        match &**lhs {
          Expression::Identifier{ name } => {
            self.replacements.insert(name.clone(), *rhs.clone());
            Expression::Statement(Box::new(Statement::None))
          }
          _ => Expression::Binop {
            lhs: lhs.clone(),
            rhs: Box::new(self.inline_expression(rhs)),
            op: op.clone(),
          }
        }
      },
      Expression::Binop{ lhs, rhs, op } => Expression::Binop {
        lhs: Box::new(self.inline_expression(lhs)),
        rhs: Box::new(self.inline_expression(rhs)),
        op: op.clone(),
      },
      Expression::Forall{ bindings, condition } => Expression::Forall {
        bindings: bindings.clone(),
        condition: Box::new(self.inline_expression(condition)),
      },
      Expression::SketchHole => Expression::SketchHole,
      Expression::Statement(stmt) => {
        Expression::Statement(Box::new(self.inline_statement(stmt)))
      }
    }
  }

  pub fn inline_block_item(&mut self, item: &BlockItem) -> BlockItem {
    match item {
      BlockItem::Declaration(decl) => self.add_declaration(decl),
      BlockItem::Statement(stmt) => BlockItem::Statement(self.inline_statement(stmt)),
    }
  }

  fn add_declaration(&mut self, decl: &Declaration) -> BlockItem {
    match &decl.initializer {
      None => BlockItem::Statement(Statement::None),
      Some(Initializer::Expression(expr)) => match &decl.declarator {
        Declarator::Identifier{ name } => {
          self.replacements.insert(name.clone(), expr.clone());
          BlockItem::Statement(Statement::None)
        },
        _ => BlockItem::Declaration(decl.clone()),
      },
      Some(Initializer::List(_)) => BlockItem::Declaration(decl.clone()),
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::crel::parser::parse_c_string;

  #[test]
  fn test_inline_expression() {
    let input_string =
      "void gen() {
         int _out;
         int  _pac_sc_s30=0;
         if ((16) < (r_handValue_in)) {
         int _out;
           _pac_sc_s30 = 1;
         } else {
         int _out;
           _pac_sc_s30 = 5;
         }
         int  _pac_sc_s30_0=0;
         if ((r_handValue_in) < (r_handValue)) {
         int _out;
           _pac_sc_s30_0 = 2;
         } else {
         int _out;
           _pac_sc_s30_0 = 1;
         }
         _out = _pac_sc_s30 * _pac_sc_s30_0;
         return _out;
       }".to_string();
    let crel = parse_c_string(input_string);

    let expected_s30 = Box::new(Expression::Ternary {
        condition: Box::new(Expression::Binop {
          lhs: Box::new(Expression::ConstInt(16)),
          rhs: Box::new(Expression::Identifier{ name: "r_handValue_in".to_string() }),
          op: BinaryOp::Lt,
        }),
        then: Box::new(Expression::ConstInt(1)),
        els: Box::new(Expression::ConstInt(5)),
      });

    let expected_s30_0 = Box::new(Expression::Ternary {
        condition: Box::new(Expression::Binop {
          lhs: Box::new(Expression::Identifier{ name: "r_handValue_in".to_string() }),
          rhs: Box::new(Expression::Identifier{ name: "r_handValue".to_string() }),
          op: BinaryOp::Lt,
        }),
        then: Box::new(Expression::ConstInt(2)),
        els: Box::new(Expression::ConstInt(1)),
      });

    let expected_body = Statement::Compound(vec!(
      BlockItem::Statement(Statement::Expression(
        Box::new(Expression::Binop {
          lhs: expected_s30.clone(),
          rhs: expected_s30_0.clone(),
          op: BinaryOp::Mul,
        })
      ))
    ));

    let expected = CRel::Seq(vec!(CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "gen".to_string(),
      params: Vec::new(),
      body: Box::new(expected_body),
    }));

    let actual = CRelInliner::new().inline_crel(&crel);
    assert_eq!(actual, expected);
  }
}
