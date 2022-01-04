use egg::{rewrite as rw, *};

use crate::analysis::*;
use crate::lang::*;
use crate::EGraph;

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| is_var(v2)(egraph, id, subst)
        && egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn free(x: Var, b: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        if let Some(v) = egraph[subst[x]].data.free.iter().next() {
            egraph[subst[b]].data.free.contains(&v)
        } else { true } // TODO should this be true?
    }
}

fn not_free(x: Var, b: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let f = free(x, b);
    move |egraph, id, subst| !f(egraph, id, subst)
}

fn is_const(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| !is_var(v)(egraph, id, subst)
}

fn is_var(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| !egraph[subst[v]].data.free.is_empty()
}

// Capture-avoiding substitution

pub struct CaptureAvoid {
    fresh: Var,
    v2: Var,
    e: Var,
    if_not_free: Pattern<USr>,
    if_free: Pattern<USr>,
}

impl Applier<USr, UAnalysis> for CaptureAvoid {
    fn apply_one(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst, searcher_ast: Option<&PatternAst<USr>>, rule_name: Symbol) -> Vec<Id> {
    let e = subst[self.e];
        let v2 = egraph[subst[self.v2]].data.free.iter().next().unwrap();
        let v2_free_in_e = egraph[e].data.free.contains(&v2);
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = egraph.add(USr::Symbol(format!("_{}", eclass).into()));
            subst.insert(self.fresh, sym);
            self.if_free.apply_one(egraph, eclass, &subst, None, "capture-avoid".parse().unwrap())
        } else {
            self.if_not_free.apply_one(egraph, eclass, &subst, None, "capture-avoid".parse().unwrap())
        }
    }
}

// Rename summation variable and push down sum

pub struct RenameSig {
    fresh: Var,
    e: Pattern<USr>,
}

impl Applier<USr, UAnalysis> for RenameSig {
    fn apply_one(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst, searcher_ast: Option<&PatternAst<USr>>, rule_name: Symbol) -> Vec<Id> {
        let mut subst = subst.clone();
        let sym = egraph.add(USr::Symbol(format!("_{}", eclass).into()));
        subst.insert(self.fresh, sym);
        self.e.apply_one(egraph, eclass, &subst, None, "rename-sig".parse().unwrap())
    }
}

// One way destructive rewrite

pub struct Destroy<A: Applier<USr, UAnalysis>> {
    e: A,
}

impl<A: Applier<USr, UAnalysis>> Applier<USr, UAnalysis> for Destroy<A> {
    fn apply_one(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst, searcher_ast: Option<&PatternAst<USr>>, rule_name: Symbol) -> Vec<Id> {
        egraph[eclass].nodes.clear();
        self.e.apply_one(egraph, eclass, subst, None, "destroy".parse().unwrap())
    }
}

fn rw_1(
    name: &'static str,
    lhs: &'static str,
    rhs: &'static str,
) -> Rewrite<USr, UAnalysis> {
    Rewrite::new(
        name,
        lhs.parse::<Pattern<USr>>().unwrap(),
        Destroy {
            e: rhs.parse::<Pattern<USr>>().unwrap(),
        },
    )
    .unwrap()
}

pub fn rules() -> Vec<Rewrite<USr, UAnalysis>> {
    // USr axioms
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

    // let rules
    rls.extend(vec![
        rw!("let-const"; "(let ?v ?e ?c)" => "?c" if is_const(var("?c"))),
        rw!("let-var-same"; "(let ?v1 ?e ?v1)" => "?e"),
        rw!("let-var-diff"; "(let ?v1 ?e ?v2)" => "?v2"
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-sig-same"; "(let ?v1 ?e (sig ?v1 ?body))" => "(sig ?v1 ?body)"),
        rw!("let-sig-diff";
            "(let ?v1 ?e (sig ?v2 ?body))" =>
            { CaptureAvoid {
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(sig ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(sig ?fresh (let ?v1 ?e (let ?v2 ?fresh ?body)))".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-add";    "(let ?v ?e (+ ?a ?b))" => "(+ (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-add-r";  "(+ (let ?v ?e ?a) (let ?v ?e ?b))" => "(let ?v ?e (+ ?a ?b))"),
        rw!("let-eq";     "(let ?v ?e (= ?a ?b))" => "(= (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-eq-r";   "(= (let ?v ?e ?a) (let ?v ?e ?b))" => "(let ?v ?e (= ?a ?b))"),
    ]);

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
        rw!("7";   "(sig ?t (+ ?a ?b))" => "(+ (sig ?t ?a) (sig ?t ?b))"),
        rw!("7-r"; "(+ (sig ?t ?a) (sig ?t ?b))" => "(sig ?t (+ ?a ?b))"),
        rw!("8"; "(sig ?s (sig ?t ?a))" => "(sig ?s (sig ?t ?a))"),
        // TODO fix this
        rw!("9";   "(* ?x (sig ?t ?y))" => "(sig ?t (* ?x ?y))"),
        rw!("9-bound";   "(* ?b (sig ?x ?a))" => "(sig ?x (* ?b ?a))"
                if not_free(var("?x"), var("?b"))),
        rw!("9-bound-r"; "(sig ?x (* ?b ?a))" => "(* ?b (sig ?x ?a))"
                if not_free(var("?x"), var("?b"))),
        rw!("9-free";
            "(* ?b (sig ?x ?a))" =>
            { RenameSig {
                fresh: var("?fresh"),
                e: "(sig ?fresh (* ?b (let ?x ?fresh ?a)))".parse().unwrap()
            }}
            if free(var("?x"), var("?b"))),
        rw!("9-r"; "(sig ?t (* ?x ?y))" => "(* ?x (sig ?t ?y))"),
        rw!("10";   "(s (sig ?t ?a))" => "(s (sig ?t (s ?a)))"),
        rw!("10-r"; "(s (sig ?t (s ?a)))" => "(s (sig ?t ?a))"),
    ]);

    // conditional axioms
    rls.extend(vec![
        rw!("eq-comm"; "(= ?x ?y)" => "(= ?y ?x)"),
        rw!("neq";   "(not (= ?x ?y))" => "(!= ?x ?y)"),
        rw!("neq-r"; "(!= ?x ?y)" => "(not (= ?x ?y))"),

        rw!("11";   "([ ?b)" => "(s ([ ?b))"),
        rw!("11-r";   "(s ([ ?b))" => "([ ?b)"),
        rw!("12"; "(+ ([ (= ?a ?b)) ([ (!= ?a ?b)))"=>"1"),
        // TODO fix this
        // rw!("13"; "(* (f ?x) ([ (= ?x ?y)))" => "(* (f ?y) ([ (= ?x ?y)))"),
        // TODO fix this
        // rw!("14"; "(sig ?t ([ (= ?t ?e)))" => "1"),
    ]);
    
    rls
}
