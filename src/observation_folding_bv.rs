use std::collections::BTreeMap;
use std::fmt::Display;
use std::str::FromStr;

use egg::Analysis;
use egg::DidMerge;
use egg::Id;
use egg::Language;

use crate::grammar::Observations;
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
pub struct ObsId (i32);

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
            if let Ok(a) = s[1..].parse::<i32>(){
                return Ok(ObsId(a));
            }
        }
        return Err(format!("Bad ObsId {}", s));

    }
}

#[derive(Debug,Default)]
pub struct ConstantFoldBV {
    assignments: Vec<Assignment<BVValue>>,
    obs_id: BTreeMap<Observations<BVValue>, ObsId>,
    id_obs: BTreeMap<ObsId, Observations<BVValue>>,
    id_next: i32,
}

impl ConstantFoldBV {
    fn get_id(&mut self) -> i32{
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
}


impl Analysis<BVLanguage> for ConstantFoldBV {
    type Data = Observations<BVValue>;

    fn make(egraph: &egg::EGraph<BVLanguage, Self>, enode: &BVLanguage) -> Self::Data {
        let x = |i: &Id| &egraph[*i].data;
        let assignments = &egraph.analysis.assignments;
        let new_obs = match enode {
            BVLanguage::Bool(c) => Observations(vec![BVValue::Bool(*c); assignments.len()]),
            BVLanguage::BV(lit) => Observations(vec![BVValue::BV(lit.clone()); assignments.len()]),
            _ => todo!(),
        };
        println!("Make: {:?} -> {:?}", enode, new_obs);
        
        new_obs
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
        assert_eq!(*a,b);
        DidMerge(false, false)
    }
    
    fn modify(egraph: &mut egg::EGraph<BVLanguage, Self>, id: egg::Id) {
        let new_obs = egraph[id].data.clone();
        let analysis = &mut egraph.analysis;
        let result = analysis.add_obs(new_obs);
        let added = egraph.add(BVLanguage::Obs(result));
        egraph.union(id, added);

    }
}