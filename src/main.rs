use std::borrow::{Borrow, BorrowMut};
use std::collections::BTreeSet;
use std::str::FromStr;
use egg::{Id, LanguageChildren, RecExpr};
use regex::{Match, Regex};
//use z3::ast::{Ast, Real};
//use z3::{SatResult, Solver, Config, Context};
use rsmt2::{Solver, SmtRes, Logic};
use rsmt2::parse::{IdentParser, ModelParser, SmtParser, ValueParser};
use std::fs::{DirEntry, File};
use std::fs;
use std::io::{self, BufRead};
use std::ops::Index;
use core::fmt::Debug;
use std::collections::BTreeMap;
use std::path::Path;
use smt2parser::{CommandStream, concrete, visitors};
use lexpr;
use lexpr::parse::{KeywordSyntax, Options, Read, SliceRead};
use lexpr::parse::TSymbol::Default;
use lexpr::Value;
use rsmt2::prelude::{Expr2Smt, Sym2Smt};
use smt2parser::concrete::{parse_simple_attribute_value};
use smt2parser::concrete::Sort::Simple;
use symbolic_expressions::Sexp;

use tokio::time::timeout;
use tokio::sync::oneshot;

use std::time::Duration;
use tokio::task;

use crate::grammar::{Grammar, GEnumerator};
use crate::language_bv::BVLanguage;

mod grammar;
mod language_bv;
mod observation_folding_bv;
mod language_bv_test;
mod g_enumerator_test;

pub fn write_str<W: io::Write>(w: &mut W, s: &str) -> SmtRes<()> {
    w.write_all(s.as_bytes())?;
    Ok(())
}

#[derive(Clone, Copy, Debug)]
pub struct Parser;

type Symbol = String;
type Sort = String;
type Param = (Symbol, Sort);

#[derive(Debug, Clone)]
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
    synth_init: bool,
    constraint_init: bool,
    var_init: bool,
    /// rsmt2 Solver
    solver: Solver<Parser>,
    /// lexpr list
    lexpr_list : Vec<Value>,
    /// variable list
    variables : Vec<Param>,
    var_set : BTreeSet<String>,
    /// constraint list
    constraints: Vec<String>,
    /// function list
    synth_funcs: Vec<Func>,
    /// Solution
    solved: bool,
    solution: String
}

impl Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context").field("lexpr_list", &self.lexpr_list).field("variables", &self.variables).field("constraints", &self.constraints).field("synth_funcs", &self.synth_funcs).finish()
    }
}

impl Context {
    /// Constructs a new cons cell from two values.
    pub fn new(solver: Solver<Parser>) -> Self
    {
        Context {
            synth_init: false,
            constraint_init: false,
            var_init: false,
            solver: solver,
            lexpr_list : vec![],
            variables: vec![],
            var_set: BTreeSet::new(),
            constraints: vec![],
            synth_funcs: vec![],
            solved: false,
            solution: "".to_string()
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

    if !ctx.synth_init {
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
        if !ctx.var_init{
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
    if !ctx.constraint_init {
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
            "set-logic" | "synth-fun" => {
                parse_sexp(ctx, &lexpr);
            },
            _ => {
                break;
            }
        }
    }
    ctx.synth_init = true;
}

fn parse_define(ctx: &mut Context){
    for lexpr in ctx.lexpr_list.clone(){
        let vec_sexp = lexpr.to_vec().unwrap();
        match vec_sexp[0].to_string().as_str()
        {
            "define-fun" | "check-synth" | "declare-var" => {
                parse_sexp(ctx, &lexpr);
            },
            _ => {

            }
        }
    }
    
    if !ctx.var_init{
        ctx.var_set = BTreeSet::from_iter(ctx.variables.iter().map(|x|x.0.clone()));
        println!("{:?} {:?}",ctx.var_set, ctx.variables);
    }
    
    ctx.var_init = true;
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
    ctx.constraint_init = true;

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

#[tokio::main]
async fn main() -> Result<(), String> {
    let op = run();
    //language_bv::test_bvliteral();
    // language_bv_test::test_observation_folding();
    // language_bv_test::test_enumerator();
    // g_enumerator_test::test_enumerator();
    // test_quick_verify();
    op.await;
    Ok(())
}

async fn run_once(path: DirEntry) -> Result<bool, String>{
    let path_unwrapped = path.path();
    let filename = path_unwrapped.to_str().unwrap();
    println!("Running file {}", &filename);
    let mut ctx = parse_file_and_create_ctx(filename);
    // println!("{:?}\n", ctx);
    parse_prefix(& mut ctx);
    // println!("{:?}\n", ctx);

    let mut list_cex: Vec<Vec<(String, String, String)>> = Vec::new();
    let mut candidates: Vec<(String, String, String)> = Vec::new(); // TODO: to egg
    if ctx.synth_funcs.get(0).is_none() {return Ok(false);}
    let mut g = Grammar::default();
    let synth_funcs = ctx.synth_funcs.clone();
    let func = synth_funcs.get(0).unwrap();

    // Test parsing grammar
    // grammar::test_grammar(&func.grammar);

    // g_enumerator_test::test_enumerator_sexpr(&func.grammar);
    g = Grammar::new_from_sexpr(&func.grammar);

    g.calc_terminals();
    let mut g_enum = GEnumerator::new(g.clone());
    // ctx.solver.define_fun(func.symbol.clone(), func.params.clone(), func.return_type.clone(), "#xF"); // what's this?
    // parse_define(&mut ctx);
    g_enum.reset_bank();


    loop {
        // reset bank

        // run until there is a class that might be correct
        // g_enum.one_iter();
        let mut quick_correct: Option<Id> = None;
        let mut count = 0;
        let mut candidate: RecExpr<BVLanguage> = RecExpr::default();
        while quick_correct.is_none(){
            g_enum.one_iter();
            for (id, sexp) in g_enum.one_per_class() {
                //println!("{}", sexp.to_string());
                // let correct = "(bvsub t s)".to_string();
                ctx.solver.define_fun(func.symbol.clone(), func.params.clone(), func.return_type.clone(), sexp.to_string());
                // println!("{:?}", quick_verify(&mut ctx, &list_cex));
                parse_define(&mut ctx);
                if quick_verify(&mut ctx, &list_cex){
                    //println!("sexp: {}", sexp.to_string());
                    quick_correct = Some(id);
                    candidate = sexp.clone();
                    ctx.solver.reset();
                    break;
                }
                ctx.solver.reset();
            }
            count += 1;
            println!("Quick check iteration: {}", count);
            let bank = &g_enum.bank;
            // if let Some(correct_id) = bank.lookup_expr(&RecExpr::from_str("(bvsub t s)").unwrap()) {
            //     println!("Found correct eclass: {:?}", correct_id);
            //     println!("Best from that eclass is: {}", g_enum.one_from_class(correct_id));
            //     println!("Data of that eclass is: {:?}", g_enum.get_data_from_class(correct_id));
            //     println!("Counter examples are: {:?}", g_enum.get_pts());
            // }

        }

        //let candidates = g_enum.sexp_vec_id(quick_correct.unwrap());
        println!("quick correct id: {}", quick_correct.unwrap());
        println!("number of counter examples present: {}", list_cex.len());
        //if candidates.len()==0{
        //    println!("eclass: {:?}", g_enum.bank[quick_correct.unwrap()])
        //}
        //for candidate in candidates {
        println!("Candidate: {}", candidate.to_string());
        // println!("{:?}", ctx.variables);
        // TODO: quick verify on counter example set
        // if !quick_verify(&mut ctx, &list_cex){
        //     ctx.solver.reset(); // reset needed because our function will be different.
        //     continue;
        // }
        ctx.solver.define_fun(func.symbol.clone(), func.params.clone(), func.return_type.clone(), candidate.to_string());
        parse_define(&mut ctx);
        // Get counter-example TODO: refactor into a function
        parse_constraints(&mut ctx);
        let result = ctx.solver.check_sat();
        let mut cex = Vec::new();
        match result {
            Ok(res) => {
                //println!("ok");
                if !res{
                    ctx.solved = true;
                    ctx.solution = candidate.to_string();
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
                // println!("Counter-example: {:?}", model);
                for res in &model.to_vec() {
                    if ctx.var_set.contains(&res.0) {
                        cex.push((res.0.to_string(), res.2.to_string(), res.3.to_string()));
                        println!("{} : {} -> {}", res.0, res.2, res.3);
                    }
                }
                // cex = cex.iter().filter(|x|var_set.contains(&x.0)).collect();
                g_enum.add_pts_vec(&cex);
                list_cex.push(cex);
                ctx.solver.reset();
                //break;
            },
            Err(e) => {
                println!("error {}", e);
            }
        }

        //}
        if ctx.solved{
            break;
        }
        g_enum.reset_bank();
        println!();
    }
    println!("Solution: {}", ctx.solution);
    //println!("End of {}\n", count);
    //count += 1;
    // return;
    Ok(true)
}


async fn run(){

    let paths = fs::read_dir("./test/individual").unwrap(); // "./benchmarks/lib/General_Track/bv-conditional-inverses/"
    let mut count = 0;
    for path in paths {
        let task = task::spawn(run_once(path.unwrap()));

        // Wrap the future with a `Timeout` set to expire in 10 milliseconds.
        if let Err(_) = timeout(Duration::from_secs(10), task).await {
            println!("did not receive value within 10 seconds");
        }

    }

    //let stream = CommandStream::new(&data.as_slice()[..], concrete::SyntaxBuilder, Some("".to_string()));
    //let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    println!("{}", "hello");

}


fn run_old() {

    let paths = fs::read_dir("./benchmarks/lib/General_Track/bv-conditional-inverses/individual").unwrap();

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

                g_enumerator_test::test_enumerator_sexpr(&func.grammar);
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