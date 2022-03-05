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



// define_language! {
//     enum BVLanguage {
//         // string variant with no children
//         "pi" = Pi,

//         // string variants with an array of child `Id`s (any static size)
//         // any type that implements LanguageChildren may be used here
//         "+" = Add([Id; 2]),
//         "-" = Sub([Id; 2]),
//         "*" = Mul([Id; 2]),

//         // can also do a variable number of children in a boxed slice
//         // this will only match if the lengths are the same
//         "list" = List(Box<[Id]>),

//         // string variants with a single child `Id`
//         // note that this is distinct from `Sub`, even though it has the same
//         // string, because it has a different number of children
//         "-"  = Neg(Id),

//         // data variants with a single field
//         // this field must implement `FromStr` and `Display`
//         Num(i32),
//         // language items are parsed in order, and we want symbol to
//         // be a fallback, so we put it last
//         Symbol(Symbol),
//         // This is the ultimate fallback, it will parse any operator (as a string)
//         // and any number of children.
//         // Note that if there were 0 children, the previous branch would have succeeded
//         Other(Symbol, Vec<Id>),
//     }
// }