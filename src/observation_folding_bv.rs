use std::collections::BTreeMap;
use std::fmt::Display;
use std::str::FromStr;

use egg::Analysis;
use egg::DidMerge;
use egg::Id;
use egg::Language;
use egg::merge_min;

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
    pub assignments: Vec<Assignment<BVValue>>,
    obs_id: BTreeMap<Observations<BVValue>, ObsId>,
    pub id_obs: BTreeMap<ObsId, Observations<BVValue>>,
    id_next: usize,
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

    pub fn new(assignments: Vec<Assignment<BVValue>>) -> Self {
        ConstantFoldBV {
            assignments,
            obs_id: Default::default(),
            id_obs: Default::default(),
            id_next: 0
        }
    }
}


impl Analysis<BVLanguage> for ConstantFoldBV {
    type Data = (Observations<BVValue>, usize);

    fn make(egraph: &egg::EGraph<BVLanguage, Self>, enode: &BVLanguage) -> Self::Data {
        let x = |i: &Id| &egraph[*i].data.0;
        let esize = |i: &Id| &egraph[*i].data.1;
        let assignments = &egraph.analysis.assignments;
        let analysis = &egraph.analysis;
        let new_obs = match enode {
            BVLanguage::Bool(c) => (Observations(vec![BVValue::Bool(*c); assignments.len()]), 1),
            BVLanguage::BV(lit) => (Observations(vec![BVValue::BV(lit.clone()); assignments.len()]), 1),
            BVLanguage::Var(var) => {
                // println!("{:?}", assignments);
                (Observations(assignments.iter().map(|assignment| {
                    // println!("{}", var.to_string());
                    assignment.get(&var.to_string()).unwrap().clone()
                }).collect()), 1)
            },
            BVLanguage::Obs(i) => (analysis.find_obs_from_id(*i).unwrap().clone(), 100000), // infinity 100000
            BVLanguage::BVConcat([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvconcat(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVNot([a]) => {
                let k = x(a).iter().map(|val| {
                    if let BVValue::BV(bv) = val {
                        BVValue::BV(language_bv::bvnot(bv).unwrap())
                    } else {
                        panic!("{:?} not a BV", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a))
            },
            BVLanguage::BVNeg([a]) => {
                let k = x(a).iter().map(|val| {
                    if let BVValue::BV(bv) = val {
                        BVValue::BV(language_bv::bvneg(bv).unwrap())
                    } else {
                        panic!("{:?} not a BV", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a))
            },
            BVLanguage::BVAnd([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvand(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVOr([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvor(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVMul([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvor(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVAdd([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvadd(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVSub([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvsub(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVDiv([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvudiv(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVRem([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvurem(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVShl([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvshl(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVShr([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::BV(language_bv::bvlshr(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            BVLanguage::BVUlt([a,b]) => {
                let k = x(a).iter().zip(x(b).iter()).map(|val| {
                    if let (BVValue::BV(bva), BVValue::BV(bvb)) = val {
                        BVValue::Bool(language_bv::bvult(bva, bvb).unwrap())
                    } else {
                        panic!("{:?} not two BVs", val);
                    }
                }).collect();
                (Observations(k), 1 + esize(a) + esize(b))
            },
            _ => todo!(),
        };
        // println!("Make: {:?} -> {:?}", enode, new_obs);
        
        new_obs
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        let (aobs, asize) = a;
        let (bobs, bsize) = b;
        assert_eq!(*aobs,bobs);
        merge_min(asize, bsize)
    }
    
    fn modify(egraph: &mut egg::EGraph<BVLanguage, Self>, id: egg::Id) {
        let (new_obs, new_size) = egraph[id].data.clone();
        let analysis = &mut egraph.analysis;
        let result = analysis.add_obs(new_obs);
        let added = egraph.add(BVLanguage::Obs(result));
        egraph.union(id, added);

    }
}