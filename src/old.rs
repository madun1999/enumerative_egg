// struct Assignment {
//     term_val_pairs: Vec<(Terminals, Value)> ,
//     assignment: BTreeMap<Terminals, usize>,
// }
// impl Hash for Assignment {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         self.term_val_pairs.hash(state);
//     }

// }
// impl PartialEq for Assignment {
//     fn eq(&self, other: &Self) -> bool {
//         let a: HashSet<_> = self.assignment.keys().collect();
//         let b: HashSet<_> = other.assignment.keys().collect();
//         if a != b {return false;}
//         for term in a {
//             if self.assignment.
//         }
//         self.term_val_pairs == other.term_val_pairs && self.assignment == other.assignment
//     }
// }
// impl Assignment {
//     pub fn update_pt(&mut self, term:Terminals, val:Value) {
//         match self.assignment.get(&term) {
//             Some(idx) => self.term_val_pairs[*idx] = (term, val),
//             None => {
//                 self.assignment.insert(term, self.term_val_pairs.len());
//                 self.term_val_pairs.push((term,val));
//             }
//         }
//     }
// }

// struct Observation {
//     assignment_val_pairs: Vec<(Assignment, Value)> ,
//     assignment: BTreeMap<Assignment, usize>,
// }

// impl Hash for Observation {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         self.assignment_val_pairs.hash(state);
//     }
// }
// impl Observation {
//     pub fn update_pt(&mut self, a:Assignment, val:Value) {
//         match self.assignment.get(&a) {
//             Some(idx) => self.assignment_val_pairs[*idx] = (a, val),
//             None => {
//                 self.assignment.insert(a, self.assignment_val_pairs.len());
//                 self.assignment_val_pairs.push((a,val));
//             }
//         }
//     }
// }

// pub struct Expr {
//     node: String,
//     child: Vec<Expr>
// }

// pub struct Enumerator {
//     // Something
//     BTreeMap<String<Vec<Expr>>>
// }



