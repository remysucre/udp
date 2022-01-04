// use egg::*;
// use usr::lang::*;
use usr::rewrites::*;

egg::test_fn! {
    spnf, rules(),
    "(sig t1 (sig t2 
        (* ([ (= t2 t)) 
            (* (sig t3 (* ([ (= (. t3 k) (. t1 k))) 
                        (* ([ (= (. t3 a) (. t1 a))) (R t3))))
                (* (R t2) 
                    (* ([ (= (. t1 k) (. t2 k)))
                        ([ (>= (. t1 a) 12))))))))" 
    => 
    "(sig t1 (sig t2 (sig t3
        (* ([ (= t2 t)) 
            (* ([ (= (. t1 k) (. t2 k)))
                (* ([ (>= (. t1 a) 12)) 
                    (* ([ (= (. t3 k) (. t1 k))) 
                        (* ([ (= (. t3 a) (. t1 a))) 
                            (* (R t3) 
                                (R t2))))))))))"
}
