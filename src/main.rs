mod grammar;
mod language_bv;
// // fn enumerator() -> impl Iterator<> {

// // }

// pub struct Context {
//     init: bool,
//     /// rsmt2 Solver
//     solver: Solver<Parser>,
//     /// lexpr list
//     lexpr_list : Vec<Value>,
//     /// variable list
//     variables : Vec<Param>,
//     /// constraint list
//     constraints: Vec<String>,
//     /// function list
//     synth_funcs: Vec<Func>
// }

// impl Context {
//     /// Constructs a new cons cell from two values.
//     pub fn new(solver: Solver<Parser>) -> Self
//     {
//         Context {
//             init: false,
//             solver: solver,
//             lexpr_list : vec![],
//             variables: vec![],
//             constraints: vec![],
//             synth_funcs: vec![]
//         }
//     }
// }

fn main() {
    language_bv::test_bvliteral();
}