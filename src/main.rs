use std::borrow::{Borrow, BorrowMut};
use regex::{Match, Regex};
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
use lexpr::parse::{KeywordSyntax, Options, Read, SliceRead};
use lexpr::Value;
use rsmt2::prelude::{Expr2Smt, Sym2Smt};
use smt2parser::concrete::{parse_simple_attribute_value};
use smt2parser::concrete::Sort::Simple;

mod grammar;
mod language_bv;
mod observation_folding_bv;

pub fn write_str<W: io::Write>(w: &mut W, s: &str) -> SmtRes<()> {
    w.write_all(s.as_bytes())?;
    Ok(())
}

#[derive(Clone, Copy)]
pub struct Parser;

type Symbol = String;
type Sort = String;
type Param = (Symbol, Sort);

pub struct Func{
    symbol: Symbol,
    params: Vec<Param>,
    return_type: Sort,
    grammar: Vec<Value> // TODO: find a better way to represent grammar
}

impl Func {
    /// Constructs a new cons cell from two values.
    pub fn new() -> Self
    {
        Func {
            symbol: "".to_string(),
            params: vec![],
            return_type: "".to_string(),
            grammar: vec![]
        }
    }
}

pub struct Context {
    init: bool,
    /// rsmt2 Solver
    solver: Solver<Parser>,
    /// lexpr list
    lexpr_list : Vec<Value>,
    /// variable list
    variables : Vec<Param>,
    /// constraint list
    constraints: Vec<String>,
    /// function list
    synth_funcs: Vec<Func>
}

impl Context {
    /// Constructs a new cons cell from two values.
    pub fn new(solver: Solver<Parser>) -> Self
    {
        Context {
            init: false,
            solver: solver,
            lexpr_list : vec![],
            variables: vec![],
            constraints: vec![],
            synth_funcs: vec![]
        }
    }
}

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

fn replace_variable(input: String, symbol: String, value: String) -> String{
    let formatted = format!(r"\s({})(\s|\))", symbol);
    let re = Regex::new(formatted.as_str()).unwrap();
    let mut string = input.to_string();
    let mut new_string= input.to_string().clone();
    let matches : Vec<Match>= re.find_iter(string.as_str()).collect();
    for m in matches.iter().rev(){
        new_string.replace_range(m.start()+1..m.end()-1, value.as_str());
    }
    new_string
}

fn parse_set_logic(ctx: &mut Context, sexp: & [Value]){

    let mut arg = sexp[1].as_symbol().unwrap();
    match arg{
        "BV" => {
            ctx.solver.borrow_mut().set_logic(Logic::QF_BV);
        },
        _ => {
            println!("unsupported logic: {}", arg);
        }
    }
}

fn parse_sort(sort: &concrete::Sort) -> Option<String>{
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

fn parse_synth_fun(ctx: &mut Context, sexp: & Value){
    ///
    /// (synth-fun inv
    ///     (
    ///         (s (_ BitVec 4)) (t (_ BitVec 4))
    ///    )
    ///     (_ BitVec 4)
    ///     ((Start (_ BitVec 4)))
    ///    ((Start (_ BitVec 4) (s t #x0 #x8 #x7 (bvneg Start) (bvnot Start) (bvadd Start Start) (bvsub Start Start) (bvand Start Start) (bvlshr Start Start) (bvor Start Start) (bvshl Start Start))))
    /// )
    ///  synth-fun
    ///  symbol
    ///  signature
    ///  return type
    ///  G_i ...
    ///
    let mut sexp_list = sexp.to_vec().unwrap().clone();
    let symbol = sexp_list[1].to_string();
    let signatures = sexp_list[2].to_vec().unwrap();
    let return_type = sexp_list[3].to_string();

    if !ctx.init {
        let mut func = Func::new();
        func.symbol = symbol;
        for sig in signatures {
            func.params.push((sig.to_vec().unwrap()[0].to_string(), sig.to_vec().unwrap()[1].to_string()));
        }
        func.return_type = return_type;
        for g in &sexp_list[4..] {
            // TODO: better way to store grammar
            func.grammar.push(g.clone());
        }

        ctx.synth_funcs.push(func);
    }

    println!("{}", sexp);
}

fn parse_decl_var(ctx: &mut Context, sexp: & Value){
    ///
    /// (declare-var s (_ BitVec 4))
    /// ```rust
    /// solver.declare_const( "s", "BitVec 4").unwrap();
    /// ```

    let mut command = &sexp.to_vec().unwrap()[0];
    let mut symbol = &sexp.to_vec().unwrap()[1];
    let mut sort = &sexp.to_vec().unwrap()[2];
    let mut new_sexp = format!("(declare-const {} {})", symbol.to_string(), sort.to_string());

    let stream = CommandStream::new(&new_sexp.as_bytes()[..], concrete::SyntaxBuilder, Some("".to_string()));
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();

    if let concrete::Command::DeclareConst{symbol, sort} = &commands[0]{
        // variable name
        //println!("{}", symbol.to_string());

        let var_type = parse_sort(sort).unwrap();
        //println!("{}", var_type);
        ctx.solver.declare_const(symbol.to_string(), sort.to_string()).unwrap();
        if !ctx.init{
            ctx.variables.push((symbol.to_string(), sort.to_string()));
        }

    } else { println!("wrong type of sexpr in declare-var"); }
}

fn parse_def_fun(ctx: &mut Context, sexp: & Value){
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
            params.push((symbol.to_string(), sort.to_string()));
        }
        let output_type = parse_sort(&sig.result).unwrap();
        //println!("{}", output_type);

        // function body
        //println!("{}", term.to_string());
        //let re = Regex::new(r"\s(?P<num>[0-9]|1[0-5])\s").unwrap();
        //let new_string = dec_to_hex(term.to_string());
        ctx.solver.define_fun(sig.name.to_string(), &params, &sig.result.to_string(), term.to_string()).unwrap();
        // solver.define_fun(
        //    symbol.to_string(), & [ ("a", "BitVec 4"), ("b", "BitVec 4")], "BitVec 4", "(ite (= b 0) 15 (bvudiv a b))"
        // ).unwrap();
    } else { println!("wrong type of sexpr in define-fun"); }
}

fn parse_constraint(ctx: &mut Context, sexp: & Value, ){
    ///
    /// (constraint (=> (SC s t) (l s t)))
    /// ``` rust
    /// solver.assert("(=> (SC s t) (l s t))")
    /// ```
    ///
    let mut command = &sexp.to_vec().unwrap()[0];
    let mut constraint = &sexp.to_vec().unwrap()[1];

    //ctx.solver.assert(constraint.to_string()).unwrap();
    if !ctx.init {
        ctx.constraints.push(constraint.to_string());
    }
}

fn parse_sexp(ctx: & mut Context, sexp: &Value){
    //println!("{}", sexp);
    let vec_sexp = sexp.to_vec().unwrap();
    match vec_sexp[0].to_string().as_str()
    {
        "set-logic" => {
            parse_set_logic(ctx, &vec_sexp);
        },
        "synth-fun" => {
            parse_synth_fun(ctx, &sexp);
        },
        "declare-var" => {
            // Variable maybe need to be stored specially
            parse_decl_var(ctx, &sexp);
        },
        "define-fun" => {
            parse_def_fun(ctx, &sexp);
        },
        "constraint" =>{
            parse_constraint(ctx, &sexp);
        },
        "check-synth" =>{
            // do nothing?
        }
        _ => {
            println!("unhandled command: {}", sexp.to_string())
        }
    }
}

fn parse_prefix(ctx: &mut Context){
    for lexpr in ctx.lexpr_list.clone(){
        let vec_sexp = lexpr.to_vec().unwrap();
        match vec_sexp[0].to_string().as_str()
        {
            "set-logic" | "synth-fun" | "declare-var"=> {
                parse_sexp(ctx, &lexpr);
            },
            _ => {
                break;
            }
        }
    }
}

fn parse_define(ctx: &mut Context){
    for lexpr in ctx.lexpr_list.clone(){
        let vec_sexp = lexpr.to_vec().unwrap();
        match vec_sexp[0].to_string().as_str()
        {
            "define-fun" | "check-synth" => {
                parse_sexp(ctx, &lexpr);
            },
            _ => {

            }
        }
    }
}

fn parse_constraints(ctx: &mut Context){
    for lexpr in ctx.lexpr_list.clone(){
        let vec_sexp = lexpr.to_vec().unwrap();
        match vec_sexp[0].to_string().as_str()
        {
            "constraint" => {
                parse_sexp(ctx, &lexpr);
            },
            _ => {

            }
        }
    }

    // invert constraints and input assert
    let mut cons_str = "".to_owned();
    for con_str in &ctx.constraints[1..]{
        cons_str.push_str("(");
        cons_str.push_str("or ");
    }
    let mut first = &ctx.constraints[0];
    cons_str.push_str("(not ");
    cons_str.push_str(first.as_str());
    cons_str.push_str(") ");

    for con_str in &ctx.constraints[1..]{

        cons_str.push_str("(not ");
        cons_str.push_str(con_str.as_str());
        cons_str.push_str("))");
    }
    println!("{}", cons_str);
    ctx.solver.assert(cons_str);
}

fn parse_file_and_create_ctx(filename: &str) -> Context{
    let mut ctx = Context::new(Solver::default_z3(Parser).unwrap());
    //ctx.solver.tee(File::create("./log.txt").unwrap());
    println!("Parsing {}", filename);
    //let filename = "./benchmarks/lib/General_Track/bv-conditional-inverses/find_inv_bvsge_bvadd_4bit.sl";
    // Consumes the iterator, returns an (Optional) String
    let data = fs::read(filename).expect("Unable to read file");
    let mut lexpr_ = lexpr::Parser::from_slice(data.as_slice());
    loop {
        let mut next_value = lexpr_.next_value();
        match next_value {
            Ok(v) => {
                match v {
                    Some(sexp) => {
                        ctx.lexpr_list.push(sexp);
                        //parse_sexp(solver, &sexp);
                    }
                    None => {
                        break;
                    }
                }
            }
            Err(e) => break,
        }
    }
    ctx
}

fn quick_verify(ctx: &mut Context, list_cex: &Vec<Vec<(String, String, String)>>)->bool{
    // (symbol, type, value)
    // use simplify

    if list_cex.len() == 0{
        return true;
    }

    // compose other constraints
    let mut cons_str = "".to_owned();
    for con_str in &ctx.constraints[1..]{
        cons_str.push_str("(");
        cons_str.push_str("and ");
    }
    let mut first = &ctx.constraints[0];
    //cons_str.push_str("");
    cons_str.push_str(first.as_str());
    //cons_str.push_str("");

    for con_str in &ctx.constraints[1..]{

        //cons_str.push_str("(");
        cons_str.push_str(" ");
        cons_str.push_str(con_str.as_str());
        //cons_str.push_str("))");
        cons_str.push_str(") ");
    }
    //println!("{}", cons_str);

    for cex in list_cex{
        let mut input_str = cons_str.clone();
        for var in cex{
            input_str = replace_variable(input_str, var.0.to_string(), var.2.to_string());
        }
        //println!("{}",input_str);
        let res = ctx.solver.simplify(input_str, ()).unwrap();
        if !res{
            return false;
        }
    }
    true
}

// pub struct Context {
//     init: bool,
//     /// rsmt2 Solver
//     solver: Solver<Parser>,
//     /// lexpr list
//     lexpr_list : Vec<Value>,
//     /// variable list
//     variables : Vec<Param>,
//     /// constraint list
//     constraints: Vec<String>,
//     /// function list
//     synth_funcs: Vec<Func>
// }

// impl Context {
//     /// Constructs a new cons cell from two values.
//     pub fn new(solver: Solver<Parser>) -> Self
//     {
//         Context {
//             init: false,
//             solver: solver,
//             lexpr_list : vec![],
//             variables: vec![],
//             constraints: vec![],
//             synth_funcs: vec![]
//         }
//     }
// }

fn main() {
    run();
    //language_bv::test_bvliteral();
}

fn run() {

    let paths = fs::read_dir("./benchmarks/lib/General_Track/bv-conditional-inverses/").unwrap();

    for path in paths {
        let mut ctx = parse_file_and_create_ctx(path.unwrap().path().to_str().unwrap());
        parse_prefix(& mut ctx);
        let mut list_cex: Vec<Vec<(String, String, String)>> = Vec::new();
        let mut candidates: Vec<(String, String, String)> = Vec::new(); // TODO: to egg
        loop {
            /// TODO: enumerate new solution
            /// candidates.push(?);

            for func in &ctx.synth_funcs {
                // Test parsing grammar
                // grammar::test_grammar(&func.grammar);
                ctx.solver.define_fun(func.symbol.clone(), func.params.clone(), func.return_type.clone(), "#xF");
            }

            // parse defined functions
            parse_define(&mut ctx);

            // TODO: quick verify on counter example set
            if !quick_verify(&mut ctx, &list_cex){
                ctx.solver.reset(); // reset needed because our function will be different.
                continue;
            }

            // Get counter-example TODO: refactor into a function
            parse_constraints(&mut ctx);
            ctx.init = true;
            let result = ctx.solver.check_sat();
            let mut cex = Vec::new();
            match result {
                Ok(res) => {
                    //println!("ok");
                    if !res{
                        println!("No counter-example");
                        break;
                    }
                    let model = ctx.solver.get_model().unwrap();
                    //`Vec<(std::string::String, Vec<(std::string::String, std::string::String)>, std::string::String, std::string::String)>`
                    /// "s", [], "(_ BitVec 4)", "#xd"
                    /// "t", [], "(_ BitVec 4)", "#x5"
                    /// "min", [], "(_ BitVec 4)", "(bvnot (bvlshr (bvnot #x0) #x1))" ??
                    /// "max", [], "(_ BitVec 4)", "(bvnot (bvnot (bvlshr (bvnot #x0) #x1)))" ??

                    println!("Counter-example:");
                    let range = ctx.variables.len();
                    for res in &model.to_vec()[..range] {
                        cex.push((res.0.to_string(), res.2.to_string(), res.3.to_string()));
                        println!("{} : {} -> {}", res.0, res.2, res.3);
                    }
                    list_cex.push(cex);
                    ctx.solver.reset();
                },
                Err(e) => {
                    println!("error {}", e);
                }
            }
        }
        println!("End");

    }

    //let stream = CommandStream::new(&data.as_slice()[..], concrete::SyntaxBuilder, Some("".to_string()));
    //let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    println!("{}", "hello");

}


