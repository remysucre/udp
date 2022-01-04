use egg::*;
use usr::rewrites::*;

fn main() {
    let start = "(sig t1 (sig t2 (sig t3
        (* ([ (= t2 t)) 
            (* ([ (= (. t1 k) (. t2 k)))
                (* ([ (>= (. t1 a) 12)) 
                    (* ([ (= (. t3 k) (. t1 k))) 
                        (* ([ (= (. t3 a) (. t1 a))) 
                            (* (R t3) 
                                (R t2))))))))))".parse().unwrap();
    let mid = "(sig t1 (sig t2 
        (* ([ (= t2 t)) 
            (* (* ([ (= (. t1 k) (. t2 k)))
                        ([ (>= (. t1 a) 12))) 
                        (sig t3 (* (* ([ (= (. t3 k) (. t1 k))) 
                        (* ([ (= (. t3 a) (. t1 a))) (R t3)))
                (R t2)))))))".parse().unwrap();
    let end = "(sig t1 (sig t2 
        (* ([ (= t2 t)) 
            (* (sig t3 (* ([ (= (. t3 k) (. t1 k))) 
                        (* ([ (= (. t3 a) (. t1 a))) (R t3))))
                (* (R t2) 
                    (* ([ (= (. t1 k) (. t2 k)))
                        ([ (>= (. t1 a) 12))))))))".parse().unwrap();
    let runner = Runner::default()
        .with_expr(&start)
        .with_expr(&mid)
        .with_expr(&end)
        .run(&rules());
    assert_eq!(runner.egraph.find(runner.roots[0]), runner.egraph.find(runner.roots[2]));
}
