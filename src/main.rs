use egg::{rewrite as rw, *};

define_language! {
    enum Usr {
        Num(i32),

        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),

        "not" = Neg(Id),
        "s" = Sqs(Id),

        "sig" = Sig(Id),
        "sum" = Sum([Id; 2]),

        "app" = App([Id; 2]),
        "lam" = Lam([Id; 2]),
        "let" = Let([Id; 3]),

        Symbol(egg::Symbol),
    }
}

type UAnalysis = ();

fn rules() -> Vec<Rewrite<Usr, UAnalysis>> {
    // semiring axioms
    let mut rls = vec![
        rw!("assoc-add";   "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-add-r"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("assoc-mul";   "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("assoc-mul-r"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),

        rw!("comm-add";  "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("comm-mul";  "(* ?a ?b)" => "(* ?b ?a)"),
        
        rw!("zero-add"; "(+ ?a 0)" => "?a"),
        rw!("zero-mul"; "(* ?a 0)" => "0"),
        rw!("one-mul";  "(* ?a 1)" => "?a"),
    
        rw!("add-zero"; "?a" => "(+ ?a 0)"),
        rw!("mul-one";  "?a" => "(* ?a 1)"),

        rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),    
    ];

    // squash axioms
    rls.extend(vec![
        rw!("1-a";   "(s 0)" => "0"),
        rw!("1-a-r"; "0" => "(s 0)"),
        rw!("1-b"; "(s (+ 1 ?x))" => "1"),
        rw!("2";   "(s (+ (s ?x) ?y))" => "(s (+ ?x ?y))"),
        rw!("2-r"; "(s (+ ?x ?y))" => "(s (+ (s ?x) ?y))"),
        rw!("3";   "(* (s ?x) (s ?y))" => "(s (* ?x ?y))"),
        rw!("3-r"; "(s (* ?x ?y))" => "(* (s ?x) (s ?y))"),
        rw!("4";   "(* (s ?x) (s ?x))" => "(s ?x)"),
        rw!("4-r"; "(s ?x)" => "(* (s ?x) (s ?x))"),
        rw!("5";   "(* ?x (s ?x))" => "?x"),
        rw!("5-r"; "?x" => "(* ?x (s ?x))"),
        rw!("6";   "(s ?x)" => "?x" if ConditionEqual::parse("?x", "(* ?x ?x))")),
        rw!("6-r"; "?x" => "(s ?x)" if ConditionEqual::parse("?x", "(* ?x ?x))")),
    ]);

    // negation axioms
    rls.extend(vec![
        rw!("n-1";   "(not 0)" => "1"),
        rw!("n-1-r"; "1" => "(not 0)"),
        rw!("n-2";   "(not (* ?x ?y))" => "(s (+ (not ?x) (not ?y)))"),
        rw!("n-2-r"; "(s (+ (not ?x) (not ?y)))" => "(not (* ?x ?y))"),
        rw!("n-3";   "(not (+ ?x ?y))" => "(* (not ?x) (not ?y))"),
        rw!("n-3-r"; "(* (not ?x) (not ?y))" => "(not (+ ?x ?y))"),
        rw!("n-4-a"; "(not (s ?x))" => "(s (not ?x))"),
        rw!("n-4-b"; "(s (not ?x))" => "(not ?x)"),
        rw!("n-4-c"; "(not ?x)" => "(not (s ?x))"),
    ]);

    // summation axioms
    rls.extend(vec![

    ]);
    
    rls
}

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
