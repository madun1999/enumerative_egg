
use std::collections::BTreeMap;
use std::collections::HashSet;
use egg::Id;
use egg::SymbolLang;
use egg::EGraph;

type Expr = SymbolLang;
type NonTerminals = String;
pub type Observations<V> = BTreeMap<Assignment<V>, V>;
type Terminals = String;
type Prod = Vec<String>;
type Prods = Vec<Prod>;
type Value = ();
type Assignment<V> = BTreeMap<Terminals, V>;





#[derive(Debug, Clone)]
pub struct Grammar {
    rules: BTreeMap<String, Prods>,
    started_enumeration: bool,
    terminals: HashSet<(NonTerminals,Terminals)>,  
    non_terminals: HashSet<NonTerminals>, 
    start: String
}
pub struct GEnumerator<V> {
    term_val_to_id: BTreeMap<Terminals, BTreeMap<Observations<V>, Id>>,
    pts: Vec<Assignment<V>>,
    grammar: Grammar,
    bank: EGraph<SymbolLang, ()>,
    nterm_obs_to_ids: BTreeMap<NonTerminals,BTreeMap<Observations<V>, Id>>,
}

impl <V> Iterator for GEnumerator<V> {

    type Item = Expr;
    fn next(&mut self) -> Option<Expr> {
        // if !self.grammar.started_enumeration {
        //     self.grammar.calc_terminals();
        //     for (non_term, term) in self.grammar.terminals { // TODO: use non_term
        //         let sync_term = SymbolLang::leaf(term.clone());
        //         let id = self.bank.add(sync_term.clone()); //TODO: remove clone
        //         let obs = self.grammar.evaluate_all(sync_term, self.pts);
                
        //         self.nterm_obs_to_ids.entry(non_term)
        //             .or_insert(Default::default())
        //             .insert(self.grammar.evaluate_all(sync_term, self.pts), id);

        //     }
        //     self.bank.rebuild();
        
        // }
        
        // Initialize list of new eclasses
        // For each production Term -> Vec<String> with terminals A1, A2, .., Ak on the rhs
        //   let a be the NonTerm vector in the rhs (size k)
        //   let b be the Term -> Vec<Id> BTree
        //   for <p1, p2, .., pk> in b[A1] x b[A2] x .. x b[An]:
        //       add rhs[A1 -> p1, .. , Ak -> pk] to the list of new eclasses
        // Add all new eclasses to bank
        // rebuild bank
        // return &bank 
        // 
        return None;
    }
}

impl <V> GEnumerator<V> {
    pub fn new(grammar: Grammar) -> GEnumerator<V> {
        GEnumerator { 
            bank: Default::default(),
            term_val_to_id: Default::default(),
            pts: vec![],
            grammar: grammar,
            nterm_obs_to_ids: Default::default(),
        } 
    }
    pub fn add_pts(&mut self, a: Assignment<V>) { // TODO: reset Genumerator
        self.pts.push(a);
    }
}


impl Grammar {
    pub fn new(rules: BTreeMap<NonTerminals, Vec<Vec<String>>>, start: String) -> Grammar {

        Grammar { 
            rules: rules, 
            started_enumeration: false, 
            terminals: Default::default(),
            non_terminals: Default::default(),
            start: start,
        } 
    } 
    pub fn add_rule(&mut self, non_term: NonTerminals, prod: Vec<String>) {
        if self.started_enumeration {
            eprintln!("Should not add rule after enumeration starts.");
        }
        self.rules.entry(non_term).or_insert(Vec::new()).push(prod);
    }
    pub fn calc_non_terminals(&mut self) {
        if !self.started_enumeration {
            self.started_enumeration = true;
            self.non_terminals = HashSet::from_iter(self.rules.keys().cloned())
        } else {
            eprintln!("Should not calc_non_terminals after enumeration starts.");
        }
    }

    pub fn calc_terminals(&mut self) {
        if !self.started_enumeration {
            self.started_enumeration = true;
            self.calc_non_terminals();
            for (non_term, prods) in self.rules.iter() { 
                for prod in prods {
                    for term in prod {
                        let p = (non_term.clone(), term.clone());
                        if !self.terminals.contains(&p) {
                            self.terminals.insert(p);  // TODO: remove clone
                            
                        }
                    } 
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

