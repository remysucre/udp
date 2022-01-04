use egg::*;
use usr::rewrites::*;

fn main() {
    let start = "(not x)".parse().unwrap();
    let runner = Runner::default()
        .with_expr(&start)
        .run(&rules());
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    println!("{}", best_expr);
    println!("{}", runner.egraph.total_size());
    println!("{:?}", runner.stop_reason.unwrap());
}
