use egg::*;

define_language! {
    pub enum USr {
        Num(i32),
        
        "var" = Var(Id),

        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "=" = Eql([Id; 2]),
        "!=" = Neq([Id; 2]),

        "not" = Neg(Id),
        "||" = Sqs(Id),
        "[]" = Cnd(Id),

        "sum" = Sum(Id),
        "sig" = Sig([Id; 2]),
        "let" = Let([Id; 3]),

        Symbol(egg::Symbol),
        Other(Symbol, Vec<Id>),
    }
}
