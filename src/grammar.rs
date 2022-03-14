
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::ops::Deref;
use std::vec;
use egg::EClass;
use egg::FromOp;
use egg::Id;

use egg::EGraph;
use itertools::Itertools;
use crate::language_bv::BVLanguage;
use crate::language_bv::BVValue;
use crate::language_bv::BV_OPS;
use crate::observation_folding_bv::ConstantFoldBV;

use lexpr;
use lexpr::parse::{KeywordSyntax, Options, Read, SliceRead};
use lexpr::Value;

type Assignment<V> = BTreeMap<String, V>;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct Terminal(pub String);
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct NonTerminal(pub String);
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Term {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct RHS(pub(crate) Vec<Term>); // assuming RHS is a flat rule, at most one terminal in front
impl RHS { 
    fn get_non_terms(&self) -> Vec<NonTerminal>{
        // return vector of nonterminals in order
        let mut res = vec![];
        for term in &self.0 {
            match term {
                Term::NonTerminal(a) => {res.push(a.clone());}
                _ => (),
            }
        }
        res
    }

    fn get_terms(&self) -> Vec<Terminal>{
        // return vector of terminals in order
        let mut res = vec![];
        for term in &self.0 {
            match term {
                Term::Terminal(a) => {res.push(a.clone());}
                _ => (),
            }
        }
        res
    }

    fn instantiate(&self, substance: Vec<&Id>, bank:&mut EGraph<BVLanguage, ConstantFoldBV>) -> BVLanguage {
        // Given rule, terms to be substituted, and 
        // substance is the terms to be inserted, term_id is a dictionary of terminal -> id 
        let mut i = 0;
        let mut skipping = 0;
        match self.0.get(0).unwrap() {
            Term::NonTerminal(a) => {skipping = 0;}
            Term::Terminal(a) => {skipping = 1;}
        }
        let children = self.0.iter().skip(skipping).map(|x| 
            match x {
                Term::NonTerminal(a) => {
                    i+=1;
                    (*substance.get(i-1).unwrap()).clone()
                }
                Term::Terminal(a) => bank.add(BVLanguage::from_op(&a.0, vec![]).unwrap())
            }
        ).collect();
        let val = match self.0.get(0).unwrap() {
            Term::Terminal(x) => &x.0,
            Term::NonTerminal(x) => &x.0,
        };
        BVLanguage::from_op(val, children).unwrap()
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Production {
    lhs: NonTerminal,
    rhs: RHS
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct Observations<V>(pub Vec<V>);

impl<V> Deref for Observations<V> {
    type Target = Vec<V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
} 


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct Grammar {
    productions: Vec<Production>,
    started_enumeration: bool,
    terminals: BTreeMap<NonTerminal,Vec<Terminal>>,  
    non_terminals: BTreeSet<NonTerminal>, 
    start: NonTerminal
}

#[derive(Debug)]
pub struct GEnumerator{ // TODO: Make it generic <L: From Op,V:Something> , BV for now
    pts: Vec<Assignment<BVValue>>,
    true_obs: Vec<Observations<BVValue>>,
    grammar: Grammar,
    bank: EGraph<BVLanguage, ConstantFoldBV>,
    started_enumeration: bool,
}

impl GEnumerator {

    pub fn one_iter(&mut self) -> &EGraph<BVLanguage, ConstantFoldBV> {
        // If not started, put all terminals in the bank
        if !self.started_enumeration {
            self.started_enumeration = true;
            for (non_terminal, terminals) in &self.grammar.terminals { // TODO: use non_term
                for terminal in terminals {
                    if !BV_OPS.contains(&terminal.0.as_str()) {
                        let sync_term= BVLanguage::from_op(&terminal.0, vec![]);
                        match sync_term {
                            Ok(a) => {
                                self.bank.add(a);
                            }
                            Err(e) => {
                                println!("{:?}", e)
                            }
                        }
                    }
                   
                }
            }
            self.bank.rebuild();
        
        } else {
            let mut new_enodes:Vec<BVLanguage> = vec![];
            for prod in &self.grammar.productions { // TODO: support different nonterminals
                // For each production Term -> Vec<String> with terminals A1, A2, .., Ak on the rhs
                //   let non_terms be the NonTerm vector in the rhs (size k)
                let non_terms = &prod.rhs.get_non_terms();
                let rhs = &prod.rhs;
                let k = non_terms.len();
                let mut term_to_ids :BTreeMap<NonTerminal, Vec<Id>> = Default::default();
                term_to_ids.insert(NonTerminal("Start".to_string()), self.bank.classes().map(|x| x.id).collect());
                // let a  = non_terms.iter().map(|x| term_to_ids.get(x).unwrap()).multi_cartesian_product();
                for substance in non_terms.iter().map(|x| term_to_ids.get(x).unwrap()).multi_cartesian_product() {
                    //   for <p1, p2, .., pk> in b[A1] x b[A2] x .. x b[An]:
                    //       add rhs[A1 -> p1, .. , Ak -> pk] to the list of new enodes
                    new_enodes.push(rhs.instantiate(substance, &mut self.bank));
                }
            }    

            
            // Add all new enodes to bank
            for enode in new_enodes {
                self.bank.add(enode);
            }
            // rebuild bank
            self.bank.rebuild();
        }

        // return &bank     
        return &self.bank;
    }
}

impl GEnumerator{
    pub fn new(grammar: Grammar) -> GEnumerator{
        
        GEnumerator { 
            bank: EGraph::new(ConstantFoldBV::default()),
            pts: vec![],
            grammar: grammar,
            true_obs: vec![],
            started_enumeration: false,
            
        } 
    }
    pub fn add_pts(&mut self, a: Assignment<BVValue>) {
        // Call reset bank after adding all the pts
        self.pts.push(a);
    }
    pub fn reset_bank(&mut self) {
        // Call this after adding all the pts
        let analysis = ConstantFoldBV::new(self.pts.clone());
        self.bank = EGraph::new(analysis);
    }
}
pub trait HasOpString {
    fn get_op_string(&self) -> String;
}






impl Grammar {
    pub fn new(productions: Vec<Production>, start: String) -> Grammar {
        Grammar { 
            productions: productions, 
            started_enumeration: false, 
            terminals: Default::default(),
            non_terminals: Default::default(),
            start: NonTerminal(start),
        } 
    }

    pub fn new_from_sexpr(sexpr: &Vec<Value>) -> Grammar {

        //println!("Test parsing grammar: {}", sexpr[0]); // non-terminals
        //println!("Test parsing grammar: {}", sexpr[1]); // rules

        let mut grammar = Grammar {
            productions: Default::default(),
            started_enumeration: false,
            terminals: Default::default(),
            non_terminals: Default::default(),
            start: NonTerminal("Start".to_string()), 
        };

        //for val in sexpr[0]{ // parse non-terminal
            // val[0]: name
            // val[1]: sort
        //}

        // let bvand_t = Term::Terminal(Terminal("bvand".to_string()));
        // let bvnot_t = Term::Terminal(Terminal("bvnot".to_string()));
        // let x_t = Term::Terminal(Terminal("x".to_string()));
        // let bv_t = Term::Terminal(Terminal("#b00001111".to_string()));
        //
        // let start_nt = Term::NonTerminal(NonTerminal("Start".to_string()));
        //
        // let start = NonTerminal("Start".to_string());
        //
        // let rhs_bvand = vec![bvand_t.clone(), start_nt.clone(), start_nt.clone()];
        // let rhs_bvnot =   vec![bvnot_t.clone(), start_nt.clone()];
        // let rhs_x = (vec![x_t]);
        // let rhs_bv = (vec![bv_t]);
        //
        // let mut g = Grammar::new(Default::default(), "Start".to_string());
        // let prods = vec![
        //     rhs_bvand.clone(),
        //     rhs_bvnot.clone(),
        //     rhs_x.clone(),
        //     rhs_bv.clone()
        // ];
        // for prod in prods {
        //     g.add_rule(start.clone(), prod)
        // }

        for rule in sexpr[1].to_vec().unwrap(){ // parse rule
            let list = rule.to_vec().unwrap();
            // rule[0]: non-terminal name
            // rule[1]: non-terminal sort
            // rule[2]:
            //println!("Test parsing grammar: {}", list[0]);
            //println!("Test parsing grammar: {}", list[2]);
            let non_term = NonTerminal(list[0].to_string());
            let mut production = Production{ lhs: non_term.clone(), rhs: RHS(vec![])};
            //grammar.non_terminals.insert(non_term.clone());
            //grammar.terminals.insert(non_term.clone(), vec![]);

            for val in list[2].to_vec().unwrap(){
                //println!("Test parsing grammar: {}", val);
                match val{
                    Value::Number(_) | Value::Bool(_) | Value::Symbol(_) =>{
                        //grammar.terminals.get_mut(&non_term).unwrap().push(Terminal(val.to_string()));
                        grammar.add_rule(non_term.clone(), vec![Term::Terminal(Terminal(val.to_string()))]);
                        //production.rhs.0.push(Term::Terminal(Terminal(val.to_string())));
                    },
                    Value::Cons(_) => {
                        // Nothing
                        //production.rhs.0.push();
                        let mut prod = vec![Term::Terminal(Terminal(val.to_vec().unwrap()[0].to_string()))];
                        for ind in 1..val.to_vec().unwrap().len(){
                            prod.push(Term::NonTerminal(NonTerminal(val.to_vec().unwrap()[ind].to_string())));
                        }
                        grammar.add_rule(non_term.clone(), prod);
                        // if val.to_string().contains(&list[0].to_string()) {
                        //     production.rhs.0.push(Term::NonTerminal(NonTerminal(val.to_string())));
                        // }else{
                        //     grammar.terminals.get_mut(&non_term).unwrap().push(Terminal(val.to_string()));
                        //     production.rhs.0.push(Term::Terminal(Terminal(val.to_string())));
                        // }
                    }
                    _ => {
                        println!("Shouldn't happens: {} in grammar parsing", val);
                    }
                }
            }
        }

        grammar
    }

    pub fn add_rule(&mut self, non_term: NonTerminal, prod: Vec<Term>) {
        if self.started_enumeration {
            eprintln!("Should not add rule after enumeration starts.");
        }
        self.productions.push(Production { lhs: non_term, rhs: RHS(prod) });
    }

    pub fn calc_non_terminals(&mut self) { 
        if !self.started_enumeration {
            self.started_enumeration = true;
            self.non_terminals = Default::default();
            for production in &self.productions {
                self.non_terminals.insert(production.lhs.clone());

            }
        } else {
            eprintln!("Should not calc_non_terminals after enumeration starts.");
        }
    }

    pub fn calc_terminals(&mut self) {
        // calls calc_non_terminals
        // do this before getting GEnumerator
        if !self.started_enumeration {
            self.calc_non_terminals();
            self.started_enumeration = true;
            self.terminals = Default::default();
            for production in &self.productions {
                // println!("{:?}", production.rhs.get_terms());
                for term in production.rhs.get_terms() {
                    self.terminals.entry(NonTerminal("Start".to_string())).or_insert(Default::default()).push(term.clone());
                }
            }
        } else {
            eprintln!("Should not calc_terminals after enumeration starts.");
        }
    }


    // pub fn iter(&self) -> GEnumerator<V>{
    //     GEnumerator::new(self.clone())
    // }

    // pub fn evaluate(&self, expr:Expr, pt:Assignment<V>) -> Value {
    //     return () 
    // }

    // pub fn evaluate_all(&self, expr:Expr, pts:Vec<Assignment<V>>) -> Observations<V> {
    //     let mut obs:Observations = Default::default();
    //     for pt in pts {
    //         // obs.insert(pt, self.evaluate(expr, pt));
    //     }
    //     obs
    // }
    
}

pub fn test_grammar(sexpr: &Vec<Value>) {
    //let grammar = Grammar::new();
    let grammar = Grammar::new_from_sexpr(sexpr);
    //println!("wait");
}