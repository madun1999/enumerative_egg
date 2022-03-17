use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::BinaryHeap;
use std::fmt::Display;
use std::str::FromStr;

use egg::Analysis;
use egg::DidMerge;
use egg::Id;
use egg::Language;
use egg::merge_min;
use itertools::Itertools;
use symbolic_expressions::Sexp;

use crate::grammar::Observations;
use crate::language_bv;
use crate::language_bv::BVLanguage;
use crate::language_bv::BVLiteral;
use crate::language_bv::BVValue;

// #[derive(Debug, AsRef)]
// pub struct Observations<V> {
//     obs: BTreeMap<Assignment<V>, V>,

// }



type Terminals = String;

type Assignment<V> = BTreeMap<Terminals, V>;

impl<V: Display> Display for Observations<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.iter().flat_map(|x| x.fmt(f)).for_each(drop); // TODO: test this
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Default)]
pub struct ObsId (usize);

impl Display for ObsId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "$")?;
        write!(f, "{}", self.0)?;
        Ok(())
    }
}

impl FromStr for ObsId {

    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.chars().next().unwrap() == '$' {
            if let Ok(a) = s[1..].parse::<usize>(){
                return Ok(ObsId(a));
            }
        }
        return Err(format!("Bad ObsId {}", s));

    }
}

#[derive(Debug,Default, Clone)]
pub struct ConstantFoldBV {
    pub assignments: BTreeSet<Assignment<BVValue>>,
    obs_id: BTreeMap<Observations<BVValue>, ObsId>,
    pub id_obs: BTreeMap<ObsId, Observations<BVValue>>,
    id_next: usize,
    min_size_ast_count: usize,
}

impl ConstantFoldBV {
    fn get_id(&mut self) -> usize{
        let a = self.id_next;
        self.id_next += 1;
        return a;
    }

    fn add_obs(&mut self, new_obs: Observations<BVValue>) -> ObsId {
        if self.obs_id.contains_key(&new_obs) {
            return self.obs_id[&new_obs];
        } else {
            let a = ObsId(self.get_id());
            self.id_obs.insert(a, new_obs.clone());
            self.obs_id.insert(new_obs, a);
            return a;
        }
    }

    fn find_obs_from_id(&self, a: ObsId) -> Option<&Observations<BVValue>>{
        self.id_obs.get(&a)
    }

    pub fn new(assignments: BTreeSet<Assignment<BVValue>>, keep_ast: usize) -> Self {
        ConstantFoldBV {
            assignments,
            obs_id: Default::default(),
            id_obs: Default::default(),
            id_next: 0,
            min_size_ast_count: keep_ast,

        }
    }
}
// #[derive(Debug)]
// struct OrderedSexp (Sexp);

// impl Ord for OrderedSexp {

// }


// #[derive(Debug, Clone)]
// type ASTByMinSize =Vec<(usize, Sexp)>;


//     fn make_ast_by_minsize(op: String, operands: Vec<&ASTByMinSize>, length: usize) -> ASTByMinSize{
//         let operands_iters = operands.iter().map(|x| x.iter());
//         let mut heap: Vec<(usize, Vec<Sexp>)> = operands_iters.multi_cartesian_product().map(|operand|{
//             let s_size = operand.iter().fold(1, |sizes, (size, _)| sizes + size);
//             let s_operand: Vec<Sexp> = operand.iter().map(|(_, child)| child.clone()).collect();
//             (s_size, s_operand)
//         }).collect();
//         heap.sort_by_key(|(size, _)| *size);
//         heap.truncate(length);
//         heap.into_iter().map(|(size, mut children)| {
//             children.insert(0,Sexp::String(op.clone()));
//             (size,Sexp::List(children))
//         }).collect()
//     }

//     fn merge_ast_by_minsize(a: &mut ASTByMinSize, b: ASTByMinSize, length: usize) -> egg::DidMerge {
//         a.extend(b);
//         a.sort_by_key(|(size, _)| *size);
//         a.truncate(length);
//         egg::DidMerge(true, true)
//     }

type ASTByMinSize =BTreeSet<(usize, String)>;


    fn make_ast_by_minsize(op: String, operands: Vec<&ASTByMinSize>, length: usize) -> ASTByMinSize{
        let operands_iters = operands.iter().map(|x| x.iter());
        let mut heap: Vec<(usize, Vec<String>)> = operands_iters.multi_cartesian_product().map(|operand|{
            let s_size = operand.iter().fold(1, |sizes, (size, _)| sizes + size);
            let s_operand: Vec<String> = operand.iter().map(|(_, child)| child.clone()).collect();
            (s_size, s_operand)
        }).collect();
        heap.sort_by_key(|(size, _)| *size);
        heap.truncate(length);
        heap.into_iter().map(|(size, mut children)| {
            children.insert(0,op.clone());
            let mut children_string = children.join(" ");
            children_string.insert_str(0,"(");
            children_string.push_str(")");
            (size,children_string)
        }).collect()
    }

    fn merge_ast_by_minsize(a: &mut ASTByMinSize, b: ASTByMinSize, length: usize) -> egg::DidMerge {
        // println!("Merging {:?} {:?}", a, b);
        let res : ASTByMinSize = a.union(&b).take(length).cloned().collect();

        // println!("Merged into {:?}", res);
        if res.len() != a.len() {
            *a = res;
            egg::DidMerge(true, true)
        } else {
            let all_equal = res.iter().zip(a.iter()).all(|(x,y)| x == y);
            *a = res;
            egg::DidMerge(!all_equal, true)
        }
        

    }


impl Analysis<BVLanguage> for ConstantFoldBV {
    type Data = (Observations<BVValue>, ASTByMinSize);

    fn make(egraph: &egg::EGraph<BVLanguage, Self>, enode: &BVLanguage) -> Self::Data {
        // println!("Make {:?}", enode);
        let x = |i: &Id| &egraph[*i].data.0;
        let esize = |i: &Id| &egraph[*i].data.1;
        let assignments = &egraph.analysis.assignments;
        let analysis = &egraph.analysis;
        let keep_ast_count = analysis.min_size_ast_count;
        let new_obs = match enode {
            BVLanguage::Bool(c) => (Observations(vec![BVValue::Bool(*c); assignments.len()]), BTreeSet::from([(1, c.to_string())])),
            BVLanguage::BV(lit) => (Observations(vec![BVValue::BV(lit.clone()); assignments.len()]), BTreeSet::from([(1, lit.to_string())])),
            BVLanguage::Var(var) => {
                // println!("{:?}", assignments);
                (Observations(assignments.iter().map(|assignment| {
                    // println!("{}", var.to_string());
                    assignment.get(&var.to_string()).unwrap().clone()
                }).collect()), BTreeSet::from([(1, var.to_string())]))
            },
            BVLanguage::Obs(i) => (analysis.find_obs_from_id(*i).unwrap().clone(), BTreeSet::from([])),
            BVLanguage::BVConcat([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvconcat(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvconcat".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVNot([a]) => {
                let k = x(a).iter().map(|val| {
                    if let BVValue::BV(bv) = val {
                        BVValue::BV(language_bv::bvnot(bv).unwrap())
                    } else {
                        panic!("{:?} not a BV", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvnot".to_string(), vec![esize(a)], keep_ast_count))
            },
            BVLanguage::BVNeg([a]) => {
                let k = x(a).iter().map(|val| {
                    if let BVValue::BV(bv) = val {
                        BVValue::BV(language_bv::bvneg(bv).unwrap())
                    } else {
                        panic!("{:?} not a BV", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvneg".to_string(), vec![esize(a)], keep_ast_count))
            },
            BVLanguage::BVAnd([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvand(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvand".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVOr([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvor(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvor".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVMul([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvor(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvmul".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVAdd([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvadd(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvadd".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVSub([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvsub(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvsub".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVDiv([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvudiv(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvdiv".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVRem([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvurem(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvrem".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVShl([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvshl(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvshl".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVShr([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvlshr(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvlshr".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            BVLanguage::BVUlt([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::Bool(language_bv::bvult(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), make_ast_by_minsize("bvult".to_string(), vec![esize(a), esize(b)], keep_ast_count))
            },
            _ => todo!(),
        };
        // println!("Make: {:?} -> {:?}", enode, new_obs);

        new_obs
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        // println!("Merging: {:?} and {:?}", a, b);
        let (aobs, asize) = a;
        let (bobs, bsize) = b;
        assert_eq!(*aobs,bobs);
        merge_ast_by_minsize(asize, bsize, self.min_size_ast_count)
        
    }
    
    fn modify(egraph: &mut egg::EGraph<BVLanguage, Self>, id: egg::Id) {
        let new_obs = egraph[id].data.0.clone();
        let result = egraph.analysis.add_obs(new_obs.clone());
        let added = egraph.add(BVLanguage::Obs(result));
        egraph.union(id, added);
        // println!("Modify adding node with id {:?}", added);

    }
}