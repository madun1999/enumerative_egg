use z3::ast::{Ast, Real};
use z3::{SatResult, Solver, Config, Context};

fn main() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let x = Real::new_const(&ctx,"x");
    let y = Real::new_const(&ctx,"y");
    let two = Real::from_real(&ctx,2, 1);
    let ten = Real::from_real(&ctx,10, 1);
    let seven = Real::from_real(&ctx,7, 1);

    let sol = Solver::new(&ctx); //x > 2, y < 10, x + 2 * y == 7

    sol.assert(&x.gt(&two));
    sol.assert(&y.lt(&ten));
    sol.assert(&y.gt(&Real::from_real(&ctx,0, 1)));
    let two_times_y = Real::mul(&ctx, &[&two, &y]);
    let x_plus_above = Real::add(&ctx, &[&x, &two_times_y]);
    sol.assert(&x_plus_above._eq(&seven));

    assert_eq!(sol.check(), SatResult::Sat);

    println!("{}", sol.get_model().unwrap());

    println!("Hello, world!");
}
