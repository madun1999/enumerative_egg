use std::borrow::{Borrow, BorrowMut};
//use z3::ast::{Ast, Real};
//use z3::{SatResult, Solver, Config, Context};
use rsmt2::{Solver, SmtRes, Logic};
use rsmt2::parse::{IdentParser, ModelParser, SmtParser, ValueParser};
use std::fs::File;
use std::fs;
use std::io::{self, BufRead};
use std::ops::Index;
use std::path::Path;
use smt2parser::{CommandStream, concrete};
use lexpr;
use lexpr::Value;

#[derive(Clone, Copy)]
struct Parser;

impl<'a> IdentParser<String, String, &'a str> for Parser {
    // Idents ~~~~~~~^^^^^^  ^^^^^^  ^^^^^^^^~~~~ Input
    //     Types ~~~~~~~~~~~~|
    fn parse_ident(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
}

impl<'a> ModelParser<String, String, String, &'a str> for Parser {
    // Idents ~~~~~~~^^^^^^  ^^^^^^  ^^^^^^  ^^^^^^^^~~~~ Input
    //         Types ~~~~~~~~|            |~~~~~ Values
    fn parse_value(
        self, input: &'a str,
        ident: &String, params: &[(String, String)], typ: &String,
    ) -> SmtRes<String> {
        Ok(input.into())
    }
}

impl<'a, 'b> ValueParser<String, &'a str> for &'b Parser {
    fn parse_value(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
}


fn parse_set_logic(solver: & mut Solver<Parser>, arg: & str, rest: & [Value]){
    match arg{
        "BV" => {
            solver.borrow_mut().set_logic(Logic::QF_BV);
        },
        _ => {
            println!("unsupported logic: {}", arg);
        }
    }
}

fn parse_def_fun(solver: & mut Solver<Parser>, rest: & [Value]){
    ///
    /// (define-fun udivtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
    ///    (ite (= b #x0) #xF (bvudiv a b)))
    /// ```rust
    /// solver.define_fun(
    ///     symbol.to_string(), & [ ("a", "BitVec 4"), ("b", "BitVec 4")], "BitVec 4", "(ite (= b 0) 15 (bvudiv a b))"
    /// ).unwrap()
    /// ```

    //println!("{}", rest[0].as_symbol().unwrap());
    let symbol = rest[0].as_symbol().unwrap();

    // parse args ((sym1 (_ type1))(sym2 (_ type2)))
    let args = &rest[1];

    // parse out (_ type)
    let out = &rest[2];

    // parse body (any)
    let body = &rest[3];
    for sym in rest{
        println!("{}", sym);
    }

    solver.define_fun(
       symbol.to_string(), & [ ("a", "BitVec 4"), ("b", "BitVec 4")], "BitVec 4", "(ite (= b 0) 15 (bvudiv a b))"
    ).unwrap();

}

fn parse_sexp(solver: & mut Solver<Parser>, sexp: & str, rest: & [Value]){
    //println!("{}", sexp);
    match sexp
    {
        "set-logic" => {
            let mut arg = rest[0].as_symbol().unwrap();
            parse_set_logic(solver, arg, &rest[1..]);
        },
        "synth-fun" => {},
        "declare-var" => {},
        "define-fun" => {
            parse_def_fun(solver, &rest);
        },
        _ => {}
    }
}

fn main() {
    let mut solver = Solver::default_z3(Parser).unwrap();
    // File hosts must exist in current path before this produces output
    let filename = "./benchmarks/lib/General_Track/bv-conditional-inverses/find_inv_bvsge_bvadd_4bit.sl";
    // Consumes the iterator, returns an (Optional) String
    let data = fs::read(filename).expect("Unable to read file");
    let mut lexpr_ = lexpr::Parser::from_slice(data.as_slice());
    loop {
        let mut next_value = lexpr_.borrow_mut().next_value();
        match next_value {
            Ok(v) => {
                match v {
                    Some(sexp) => {
                        parse_sexp(& mut solver, sexp[0].as_symbol().unwrap(), &sexp.to_vec().unwrap()[1..]);
                    }
                    None => {
                        break;
                    }
                }
            }
            Err(e) => break,
        }
    }

    //let stream = CommandStream::new(&data.as_slice()[..], concrete::SyntaxBuilder, Some("".to_string()));
    //let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    println!("{}", "hello");


}

fn test_z3(){
    // let cfg = Config::new();
    // let ctx = Context::new(&cfg);
    //
    // let x = Real::new_const(&ctx,"x");
    // let y = Real::new_const(&ctx,"y");
    // let two = Real::from_real(&ctx,2, 1);
    // let ten = Real::from_real(&ctx,10, 1);
    // let seven = Real::from_real(&ctx,7, 1);
    //
    // let sol = Solver::new(&ctx); //x > 2, y < 10, x + 2 * y == 7
    //
    // sol.assert(&x.gt(&two));
    // sol.assert(&y.lt(&ten));
    // sol.assert(&y.gt(&Real::from_real(&ctx,0, 1)));
    // let two_times_y = Real::mul(&ctx, &[&two, &y]);
    // let x_plus_above = Real::add(&ctx, &[&x, &two_times_y]);
    // sol.assert(&x_plus_above._eq(&seven));
    //
    // assert_eq!(sol.check(), SatResult::Sat);
    //
    // println!("{}", sol.get_model().unwrap());
    //
    // println!("Hello, world!");
}