use egg::*;
use udp::lang::*;
use udp::analysis::*;
use udp::rewrites::*;

fn prove_eqs(exprs: &[&str], rls: &[Rewrite<USr, UAnalysis>]) {
    let mut runner = Runner::default();
    for e in exprs {
        runner = runner.with_expr(&e.parse().unwrap());
    }
    runner = runner.run(rls);
    // runner.egraph.dot().to_dot("g.dot").unwrap();
    for (i, _) in exprs.iter().enumerate() {
        assert_eq!(runner.egraph.find(runner.roots[0]), runner.egraph.find(runner.roots[i]));
    }
}

#[test]
fn equality_semantics() {
    prove_eqs(&vec!["(sig t (* (var t) ([] (= (var t) (var e)))))","(var e)"], &rules())
}

#[test]
fn spnf() {
    prove_eqs(&vec![
        "(sig t1 (sig t2 (sig t3
            (* ([] (= t2 t)) 
                (* ([] (= (. t1 k) (. t2 k)))
                    (* ([] (>= (. t1 a) 12)) 
                        (* ([] (= (. t3 k) (. t1 k))) 
                            (* ([] (= (. t3 a) (. t1 a))) 
                                (* (R t3) 
                                    (R t2))))))))))",
        "(sig t1 (sig t2 
            (* ([] (= t2 t)) 
                (* (* ([] (= (. t1 k) (. t2 k)))
                            ([] (>= (. t1 a) 12))) 
                            (sig t3 (* (* ([] (= (. t3 k) (. t1 k))) 
                            (* ([] (= (. t3 a) (. t1 a))) (R t3)))
                    (R t2)))))))",
        "(sig t1 (sig t2 
            (* ([] (= t2 t)) 
                (* (sig t3 (* ([] (= (. t3 k) (. t1 k))) 
                            (* ([] (= (. t3 a) (. t1 a))) (R t3))))
                    (* (R t2) 
                        (* ([] (= (. t1 k) (. t2 k)))
                            ([] (>= (. t1 a) 12))))))))",
    ], &rules())
}
