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
use smt2parser::{CommandStream, concrete, visitors};
use lexpr;
use lexpr::Value;
use smt2parser::concrete::{parse_simple_attribute_value, Sort};
use smt2parser::concrete::Sort::Simple;

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

fn parse_sort(sort: &Sort) -> Option<String>{
    if let concrete::Sort::Simple {identifier} = &sort{
        if let visitors::Identifier::Indexed {symbol, indices} = &identifier{
            //println!("{}", symbol.to_string());
            //println!("{}", indices[0].to_string());
            //println!("{}", ret_str);
            Some(format!("{} {}", symbol.to_string(), indices[0].to_string()))
        } else if let visitors::Identifier::Simple {symbol} = &identifier{
            Some(symbol.to_string())
        }
        else{
            println!("cannot parse: {}", identifier.to_string());
            None
        }
    }else{
        println!("cannot parse: {}", sort.to_string());
        None
    }
}

fn parse_def_fun(solver: & mut Solver<Parser>, sexp: & Value){
    ///
    /// (define-fun udivtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
    ///    (ite (= b #x0) #xF (bvudiv a b)))
    /// ```rust
    /// solver.define_fun(
    ///     symbol.to_string(), & [ ("a", "BitVec 4"), ("b", "BitVec 4")], "BitVec 4", "(ite (= b 0) 15 (bvudiv a b))"
    /// ).unwrap()
    /// ```

    let sexp_string = sexp.to_string();
    let stream = CommandStream::new(&sexp_string.as_bytes()[..], concrete::SyntaxBuilder, Some("".to_string()));
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();

    if let concrete::Command::DefineFun{sig, term} = &commands[0]{
        // function signature
        //println!("{}", sig.name.to_string());

        let mut params = Vec::new();
        for ( symbol, sort )  in &sig.parameters{
            //println!("{}", symbol);
            let param_type = parse_sort(sort).unwrap();
            //println!("{}",param_type);
            params.push((symbol.to_string(), param_type.to_string()));
        }
        let output_type = parse_sort(&sig.result).unwrap();
        //println!("{}", output_type);

        // function body
        //println!("{}", term.to_string());
        solver.define_fun(sig.name.to_string(), &params, output_type, term.to_string()).unwrap();
        // solver.define_fun(
        //    symbol.to_string(), & [ ("a", "BitVec 4"), ("b", "BitVec 4")], "BitVec 4", "(ite (= b 0) 15 (bvudiv a b))"
        // ).unwrap();
    } else { println!("wrong type of sexpr in define-fun"); }
}

fn parse_decl_var(solver: & mut Solver<Parser>, sexp: & Value){
    ///
    /// (declare-var s (_ BitVec 4))
    /// ```rust
    /// solver.declare_const( "s", "BitVec 4").unwrap();
    /// ```

    let mut symbol = &sexp.to_vec().unwrap()[0];
    let mut sort = &sexp.to_vec().unwrap()[1];
    let mut new_sexp = format!("(declare-const {} {})", symbol.to_string(), sort.to_string());

    let stream = CommandStream::new(&new_sexp.as_bytes()[..], concrete::SyntaxBuilder, Some("".to_string()));
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();

    if let concrete::Command::DeclareConst{symbol, sort} = &commands[0]{
        // variable name
        //println!("{}", symbol.to_string());

        let var_type = parse_sort(sort).unwrap();
        //println!("{}", var_type);
        solver.declare_const(symbol.to_string(), var_type).unwrap();

    } else { println!("wrong type of sexpr in declare-var"); }
}

fn parse_sexp(solver: & mut Solver<Parser>, sexp: &Value){
    //println!("{}", sexp);
    let vec_sexp = sexp.to_vec().unwrap();
    match vec_sexp[0].to_string().as_str()
    {
        "set-logic" => {
            let mut arg = sexp[1].as_symbol().unwrap();
            parse_set_logic(solver, arg, &vec_sexp[2..]);
        },
        "synth-fun" => {

        },
        "declare-var" => {

            // Variable maybe need to be stored specially
            parse_decl_var(solver, &sexp);
        },
        "define-fun" => {
            parse_def_fun(solver, &sexp);
        },
        "constraint" =>{

        },
        "check-synth" =>{

        }
        _ => {
            println!("unhandled command: {}", sexp.to_string())
        }
    }
}

fn parse_file(filename: &str) -> Solver<Parser>{
    let mut solver = Solver::default_z3(Parser).unwrap();
    println!("Parsing {}", filename);
    //let filename = "./benchmarks/lib/General_Track/bv-conditional-inverses/find_inv_bvsge_bvadd_4bit.sl";
    // Consumes the iterator, returns an (Optional) String
    let data = fs::read(filename).expect("Unable to read file");
    let mut lexpr_ = lexpr::Parser::from_slice(data.as_slice());
    loop {
        let mut next_value = lexpr_.borrow_mut().next_value();
        match next_value {
            Ok(v) => {
                match v {
                    Some(sexp) => {
                        parse_sexp(& mut solver, &sexp);
                    }
                    None => {
                        break;
                    }
                }
            }
            Err(e) => break,
        }
    }
    solver
}

fn main() {

    let paths = fs::read_dir("./benchmarks/lib/General_Track/bv-conditional-inverses/").unwrap();

    for path in paths {
        let mut solver = parse_file(path.unwrap().path().to_str().unwrap());
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