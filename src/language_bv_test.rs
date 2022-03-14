use std::{collections::BTreeMap, str::FromStr};

use egg::{RecExpr, EGraph, Symbol};

use crate::{language_bv::{BVLanguage, BVValue, BVLiteral}, observation_folding_bv::ConstantFoldBV};



pub fn test_observation_folding() {
    let my_expression: RecExpr<BVLanguage> = "(bvadd #xaa y)".parse().unwrap();
    println!("this is my expression {}", my_expression);


    let bv1 = BVValue::BV(BVLiteral::from_str("#b00001111").unwrap());
    let bv2 = BVValue::BV(BVLiteral::from_str("#b00110011").unwrap());
    let bv3 = BVLiteral::from_str("#b00000011").unwrap();
    let assignment1 = BTreeMap::from([
        ("x".to_string(), bv1.clone()),
        ("y".to_string(), bv2.clone())
    ]);

    let mut egraph: EGraph<BVLanguage, ConstantFoldBV> = EGraph::new(ConstantFoldBV::new(vec![assignment1]));
    let a = egraph.add(BVLanguage::Var(Symbol::from("x")));
    let b = egraph.add(BVLanguage::Var(Symbol::from("y")));
    let c = egraph.add(BVLanguage::BVAnd([a,b]));
    let c2 = egraph.add(BVLanguage::BV(bv3));
    assert_eq!(egraph.find(c), egraph.find(c2));
    assert_eq!(egraph.total_size(), 7);
    assert_eq!(egraph.number_of_classes(), 3);
    // print!("{:?}", egraph[a].sexp_vect(&egraph, &Default::default()))
}

pub fn test_enumerator() {
    let my_expression: RecExpr<BVLanguage> = "(bvadd #xaa y)".parse().unwrap();
    println!("this is my expression {}", my_expression);


    let bv1 = BVLiteral::from_str("#b00001111").unwrap();
    let bv2 = BVLiteral::from_str("#b00110011").unwrap();
    let bvv1 = BVValue::BV(BVLiteral::from_str("#b00001111").unwrap());
    let bvv2 = BVValue::BV(BVLiteral::from_str("#b00110011").unwrap());
    let bv3 = BVLiteral::from_str("#b00000011").unwrap();
    let assignment1 = BTreeMap::from([
        ("x".to_string(), bvv1.clone()),
        ("y".to_string(), bvv2.clone())
    ]);

    let mut egraph: EGraph<BVLanguage, ConstantFoldBV> = EGraph::new(ConstantFoldBV::new(vec![assignment1]));
    let a = egraph.add(BVLanguage::Var(Symbol::from("x")));
    let b = egraph.add(BVLanguage::Var(Symbol::from("y")));
    let c = egraph.add(BVLanguage::BVAnd([a,b]));
    let d = egraph.add(BVLanguage::BV(bv1));
    let e = egraph.add(BVLanguage::BV(bv2));
    let f = egraph.add(BVLanguage::BVAnd([a,a]));
    assert_eq!(egraph.rebuild(), 0);

    for id in [c,f] {
        let sexp_vec = egraph[id].sexp_vect(&egraph, &Default::default());
        let str_vec:Vec<String> = sexp_vec.iter().map(|x| x.to_string()).collect();
        println!("{:?}", str_vec);
    }
   

    
    // print!("{:?}", egraph[a].sexp_vect(&egraph, &Default::default()))


}