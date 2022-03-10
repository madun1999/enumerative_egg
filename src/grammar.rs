
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::ops::Deref;
use std::vec;
use egg::FromOp;
use egg::Id;

use egg::EGraph;
use itertools::Itertools;
use crate::language_bv::BVLanguage;
use crate::language_bv::BVValue;
use crate::language_bv::BV_OPS;
use crate::observation_folding_bv::ConstantFoldBV;


type Assignment<V> = BTreeMap<Terminal, V>;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
struct Terminal(String);
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
struct NonTerminal(String);
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Term {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct RHS(Vec<Term>); // assuming RHS is a flat rule, at most one terminal in front
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
    start: Terminal
}

pub struct GEnumerator{ // TODO: Make it generic <L: From Op,V:Something> , BV for now
    pts: Vec<Assignment<BVValue>>,
    true_obs: Vec<Observations<BVValue>>,
    grammar: Grammar,
    bank: EGraph<BVLanguage, ConstantFoldBV>,
}

impl GEnumerator {

    fn next(&mut self) -> &EGraph<BVLanguage, ConstantFoldBV> {
        // If not started, put all terminals in the bank
        if !self.grammar.started_enumeration {
            self.grammar.calc_terminals();
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
        
        }
        let mut new_enodes:Vec<BVLanguage> = vec![];
        for prod in &self.grammar.productions { // TODO: support different nonterminals
            // For each production Term -> Vec<String> with terminals A1, A2, .., Ak on the rhs
            //   let non_terms be the NonTerm vector in the rhs (size k)
            let non_terms = &prod.rhs.get_non_terms();
            let rhs = &prod.rhs;
            let k = non_terms.len();
            let mut term_to_ids :BTreeMap<NonTerminal, Vec<Id>> = Default::default();
            term_to_ids.insert(NonTerminal("Start".to_string()), self.bank.classes().map(|x| x.id).collect());
            
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
        } 
    }
    pub fn add_pts(&mut self, a: Assignment<BVValue>) { // TODO: reset Genumerator
        self.pts.push(a);
    }
}


impl Grammar {
    pub fn new(productions: Vec<Production>, start: String) -> Grammar {
        Grammar { 
            productions: productions, 
            started_enumeration: false, 
            terminals: Default::default(),
            non_terminals: Default::default(),
            start: Terminal(start),
        } 
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
        if !self.started_enumeration {
            self.calc_non_terminals();
            self.started_enumeration = true;
            self.non_terminals = Default::default();
            for production in &self.productions {
                for term in production.rhs.get_non_terms() {
                    self.non_terminals.insert(term);
                }
            }
        } else {
            eprintln!("Should not calc_non_terminals after enumeration starts.");
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

fn test_grammar() {
    
}