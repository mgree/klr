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

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Predicate(HConsed<ActualPredicate>);

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualPredicate {
    One,
    Zero,
    Par(Predicate, Predicate),
    Seq(Predicate, Predicate),
    Not(Predicate),
    Eq(Var, Expr),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Action(HConsed<ActualAction>);

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualAction {
    Pred(Predicate),
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
    let PREDICATE = consign(37) for ActualPredicate;
}

impl Predicate {
    pub fn get(&self) -> &ActualPredicate {
        self.0.get()
    }

    pub fn uid(&self) -> u64 {
        self.0.uid()
    }

    pub fn one() -> Predicate {
        Predicate(PREDICATE.mk(ActualPredicate::One))
    }
    
    pub fn zero() -> Predicate {
        Predicate(PREDICATE.mk(ActualPredicate::Zero))
    }
    
    pub fn par(p1: Predicate, p2: Predicate) -> Predicate {
        use ActualPredicate::*;
    
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
            (_, _) => Predicate(PREDICATE.mk(ActualPredicate::Par(p1, p2))),
        }
    }

    pub fn seq(p1: Predicate, p2: Predicate) -> Predicate {
        use ActualPredicate::*;
    
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
                let p12_p2 = Predicate::seq(p12.clone(), p2);
                Predicate::seq(p11.clone(), p12_p2)
            }
            (_, _) => Predicate(PREDICATE.mk(ActualPredicate::Seq(p1, p2))),
        }
    }
    
    pub fn not(p: Predicate) -> Predicate {
        use ActualPredicate::*;
    
        match p.get() {
            One => Predicate::zero(),
            Zero => Predicate::one(),
            Not(p) => p.clone(),
            _ => Predicate(PREDICATE.mk(ActualPredicate::Not(p))),
        }
    }
    
    pub fn eq(v: Var, e: Expr) -> Predicate {
        match e.get() {
            ActualExpr::Var(v2) if &v == v2 => Predicate::one(),
            _ => Predicate(PREDICATE.mk(ActualPredicate::Eq(v, e))),
        }
    }
}

consign! {
    let ACTION = consign(37) for ActualAction;
}

impl Action {
    pub fn get(&self) -> &ActualAction {
        self.0.get()
    }

    pub fn uid(&self) -> u64 {
        self.0.uid()
    }

    pub fn predicate(p: Predicate) -> Action {
        Action(ACTION.mk(ActualAction::Pred(p)))
    }

    pub fn zero() -> Action {
        Action::predicate(Predicate::zero())
    }

    pub fn one() -> Action {
        Action::predicate(Predicate::one())
    }
    
    pub fn par(a1: Action, a2: Action) -> Action {
        if a1.uid() == a2.uid() { 
            return a1; 
        }
    
        use ActualAction::*;
        match (a1.get(), a2.get()) {
            // push down predicates
            (Pred(p1), Pred(p2)) => Action::predicate(Predicate::par(p1.clone(), p2.clone())),
            // 0 + a = a + 0 = a for all actions a
            (_, Pred(p)) if p.get() == &ActualPredicate::Zero => a1,
            (Pred(p), _) if p.get() == &ActualPredicate::Zero => a2,
            // TODO: 1 + a;a* = 1 + a*;a = a*;a + 1 = a;a* + 1 = a*
            // TODO: a + pa = pa + a = a
            (_, _) => Action(ACTION.mk(Par(a1, a2))),
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
            ActualExpr::Var(v2) if &v == v2 => Action::one(),
            _ => Action(ACTION.mk(ActualAction::Assign(v, e))),
        }
    }
}



