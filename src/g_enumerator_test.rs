use std::{collections::BTreeMap, str::FromStr};

use crate::{grammar::{Grammar, RHS, Production, Term, Terminal, NonTerminal, GEnumerator}, language_bv::{BVValue, BVLiteral}};



pub fn test_enumerator() {
    let bvand_t = Term::Terminal(Terminal("bvand".to_string()));
    let bvnot_t = Term::Terminal(Terminal("bvnot".to_string()));
    let x_t = Term::Terminal(Terminal("x".to_string()));
    let bv_t = Term::Terminal(Terminal("#b00001111".to_string()));

    let start_nt = Term::NonTerminal(NonTerminal("Start".to_string()));

    let start = NonTerminal("Start".to_string());

    let rhs_bvand = vec![bvand_t.clone(), start_nt.clone(), start_nt.clone()];
    let rhs_bvnot =   vec![bvnot_t.clone(), start_nt.clone()];
    let rhs_x = (vec![x_t]);
    let rhs_bv = (vec![bv_t]);

    let mut g = Grammar::new(Default::default(), "Start".to_string());
    let prods = vec![
        rhs_bvand.clone(),
        rhs_bvnot.clone(),
        rhs_x.clone(),
        rhs_bv.clone()
    ];
    for prod in prods {
        g.add_rule(start.clone(), prod)
    }
    g.calc_terminals();
    println!("{:?}", g);

    let mut g_enum = GEnumerator::new(g.clone());
    let bv1 = BVValue::BV(BVLiteral::from_str("#b00001111").unwrap());
    let bv2 = BVValue::BV(BVLiteral::from_str("#b00110011").unwrap());
    let bv3 = BVLiteral::from_str("#b00000011").unwrap();
    let assignment1 = BTreeMap::from([
        (("x".to_string()), bv1.clone()),
        (("y".to_string()), bv2.clone())
    ]);

    let assignment2 = BTreeMap::from([
        (("x".to_string()), bv2.clone()),
        (("y".to_string()), bv1.clone())
    ]);

    g_enum.add_pts(assignment1);
    g_enum.add_pts(assignment2);
    g_enum.reset_bank();
    println!();
    println!("{:?}", g_enum);
    println!();

    for i in 0..10 {
        let bank = g_enum.one_iter();
        println!();
        println!("Generated dot file! My egraph dot file: target/foo{}.svg", i);
        // bank.dot().to_svg(format!("target/foo{}.svg", i)).unwrap();
        // println!("{:?}", bank);
        println!();
        println!("Bank has {:?} many EClasses and {:?} many ENodes", bank.number_of_classes(), bank.total_size());
    }
    
    
    // 
}