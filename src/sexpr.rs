use std::{
    fmt::{self, Display, Formatter},
    iter::Peekable,
    str::{Chars, FromStr},
};

#[derive(Debug, PartialEq)]
pub enum SExpr {
    Symbol(String),
    Expr(Vec<SExpr>),
}

impl SExpr {
    pub fn as_symbol(&self) -> &String {
        if let SExpr::Symbol(s) = self {
            s
        } else {
            panic!("Expected symbol.");
        }
    }
    pub fn as_subexpr(&self) -> &Vec<SExpr> {
        if let SExpr::Expr(items) = self {
            items
        } else {
            panic!("Expected subexpression.");
        }
    }
}

impl FromStr for SExpr {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (expr, mut rest) = parse_sexpr(s.chars().peekable());
        if rest.peek().is_some() {
            Err(format!("Leftover data: {}", rest.collect::<String>()))
        } else {
            Ok(expr)
        }
    }
}

impl Display for SExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Symbol(s) => write!(f, "{s}"),
            SExpr::Expr(sub_expr) => write!(
                f,
                "({})",
                sub_expr
                    .iter()
                    // TODO should properly write to f instead of using to_string.
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

fn parse_sexpr(mut input: Peekable<Chars>) -> (SExpr, Peekable<Chars>) {
    while *input.peek().unwrap() == ' ' {
        input.next();
    }
    if *input.peek().unwrap() == '(' {
        let mut sub = Vec::new();
        input.next();
        loop {
            while *input.peek().unwrap() == ' ' {
                input.next();
            }
            if *input.peek().unwrap() == ')' {
                break;
            }
            let (next, rest) = parse_sexpr(input);
            sub.push(next);
            input = rest;
        }
        input.next();
        (SExpr::Expr(sub), input)
    } else {
        let mut symbol = String::new();
        loop {
            if input.peek().is_none() {
                break;
            }
            let c = *input.peek().unwrap();
            if c == '(' || c == ')' || c == ' ' {
                break;
            }
            symbol.push(c);
            input.next();
        }
        (SExpr::Symbol(symbol), input)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_sexpr() {
        assert_eq!(SExpr::from_str("()").unwrap(), SExpr::Expr(vec![]));
        assert_eq!(
            SExpr::from_str("x").unwrap(),
            SExpr::Symbol("x".to_string())
        );
        assert_eq!(
            SExpr::from_str("(x)").unwrap(),
            SExpr::Expr(vec![SExpr::Symbol("x".to_string())])
        );
        assert_eq!(
            SExpr::from_str("(x y)").unwrap(),
            SExpr::Expr(vec![
                SExpr::Symbol("x".to_string()),
                SExpr::Symbol("y".to_string())
            ])
        );
        assert_eq!(
            SExpr::from_str("(x (y t) (r))").unwrap(),
            SExpr::Expr(vec![
                SExpr::Symbol("x".to_string()),
                SExpr::Expr(vec![
                    SExpr::Symbol("y".to_string()),
                    SExpr::Symbol("t".to_string()),
                ]),
                SExpr::Expr(vec![SExpr::Symbol("r".to_string()),])
            ])
        );
    }

    #[test]
    fn parse_sexpr_spaces() {
        assert_eq!(SExpr::from_str("()"), SExpr::from_str("(  )"));
        assert_eq!(SExpr::from_str("(  x (y )  )"), SExpr::from_str("(x(y))"));
        assert_eq!(
            SExpr::from_str("(  x () (y ) ( t t) )"),
            SExpr::from_str("(x()(y)(t t))")
        );
    }
}
