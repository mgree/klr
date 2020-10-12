#[macro_use]
extern crate hashconsing;
use hashconsing::{HConsed, HashConsign};
use std::hash::Hash;

use std::fmt::Debug;

pub type Var = String;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expr(HConsed<ActualExpr>);

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualExpr {
    Nat(usize),
    Var(Var),
}

pub type Pred = HConsed<ActualPred>;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualPred {
    One,
    Zero,
    Par(Pred, Pred),
    Seq(Pred, Pred),
    Not(Pred),
    Eq(Var, Expr),
}

pub type Action = HConsed<ActualAction>;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualAction {
    Pred(Pred),
    Par(Action, Action),
    Seq(Action, Action),
    Star(Action),
    Assign(Var, Expr),
}

consign! {
    let EXPR = consign(37) for ActualExpr;
}

impl Expr {
    pub fn get(&self) -> &ActualExpr {
        self.0.get()
    }

    pub fn uid(&self) -> u64 {
        self.0.uid()
    }

    pub fn nat(n: usize) -> Expr {
        Expr(EXPR.mk(ActualExpr::Nat(n)))
    }

    pub fn var(v: Var) -> Expr {
        Expr(EXPR.mk(ActualExpr::Var(v)))
    }    
}


consign! {
    let PRED = consign(37) for ActualPred;
}

pub fn pone() -> Pred {
    PRED.mk(ActualPred::One)
}

pub fn pzero() -> Pred {
    PRED.mk(ActualPred::Zero)
}

pub fn ppar(p1: Pred, p2: Pred) -> Pred {
    use ActualPred::*;

    // p + p = p (for all predicates p)
    if p1.uid() == p2.uid() {
        return p1;
    }

    match (p1.get(), p2.get()) {
        // 1 + p = p + 1 = 1, so return the 1 we have
        (One, _) => p1,
        (_, One) => p2,
        // 0 + p = p + 0 = p, so return the p we have
        (_, Zero) => p1,
        (Zero, _) => p2,
        (_, _) => PRED.mk(ActualPred::Par(p1, p2)),
    }
}

pub fn pseq(p1: Pred, p2: Pred) -> Pred {
    use ActualPred::*;

    // p;p = p (for all predicates p)
    if p1.uid() == p2.uid() {
        return p1;
    }

    match (p1.get(), p2.get()) {
        // 1;p = p;1 = p, so return the p we have
        (One, _) => p2,
        (_, One) => p1,
        // 0;p = p;0 = 0, so return the 0 we have
        (_, Zero) => p2,
        (Zero, _) => p1,
        // right associate
        (Seq(p11, p12), Seq(_, _)) => {
            let p12_p2 = pseq(p12.clone(), p2);
            pseq(p11.clone(), p12_p2)
        }
        (_, _) => PRED.mk(ActualPred::Seq(p1, p2)),
    }
}

pub fn pnot(p: Pred) -> Pred {
    use ActualPred::*;

    match p.get() {
        One => pzero(),
        Zero => pone(),
        Not(p) => p.clone(),
        _ => PRED.mk(ActualPred::Not(p)),
    }
}

pub fn peq(v: Var, e: Expr) -> Pred {
    match e.get() {
        ActualExpr::Var(v2) if &v == v2 => pone(),
        _ => PRED.mk(ActualPred::Eq(v, e)),
    }
}

consign! {
    let ACTION = consign(37) for ActualAction;
}

pub fn pred(p: Pred) -> Action {
    ACTION.mk(ActualAction::Pred(p))
}

pub fn zero() -> Action {
    pred(pzero())
}

pub fn one() -> Action {
    pred(pone())
}

pub fn par(a1: Action, a2: Action) -> Action {
    if a1.uid() == a2.uid() { 
        return a1; 
    }

    use ActualAction::*;
    match (a1.get(), a2.get()) {
        // push down predicates
        (Pred(p1), Pred(p2)) => pred(ppar(p1.clone(), p2.clone())),
        // 0 + a = a + 0 = a for all actions a
        (_, Pred(p)) if p.get() == &ActualPred::Zero => a1,
        (Pred(p), _) if p.get() == &ActualPred::Zero => a2,
        // TODO: 1 + a;a* = 1 + a*;a = a*;a + 1 = a;a* + 1 = a*
        // TODO: a + pa = pa + a = a
        (_, _) => ACTION.mk(Par(a1, a2)),
    }
}

pub fn seq(_a1: Action, _a2: Action) -> Action {
    todo!("seq")
}

pub fn star(_a: Action) -> Action {
    todo!("star")
}

pub fn assign(v: Var, e: Expr) -> Action {
    match e.get() {
        ActualExpr::Var(v2) if &v == v2 => one(),
        _ => ACTION.mk(ActualAction::Assign(v, e)),
    }
}