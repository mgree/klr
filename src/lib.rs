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

    pub fn is_zero(&self) -> bool {
        match self.get() {
            ActualPredicate::Zero => true,
            _ => false,
        }
    }

    pub fn is_one(&self) -> bool {
        match self.get() {
            ActualPredicate::Zero => true,
            _ => false,
        }
    }

    pub fn not<T>(p: T) -> Predicate
    where
        T: Into<Predicate>,
    {
        let p = p.into();
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

    pub fn is_zero(&self) -> bool {
        match self.get() {
            ActualAction::Pred(p) => p.is_zero(),
            _ => false,
        }
    }

    pub fn is_one(&self) -> bool {
        match self.get() {
            ActualAction::Pred(p) => p.is_one(),
            _ => false,
        }
    }

    pub fn predicate(p: Predicate) -> Action {
        Action(ACTION.mk(ActualAction::Pred(p)))
    }

    pub fn star<T>(a: T) -> Action
    where
        T: Into<Action>,
    {
        let a = a.into();

        use ActualAction::*;
        match a.get() {
            Pred(_) => Action::one(),
            Star(_) => a,
            _ => Action(ACTION.mk(ActualAction::Star(a))),
        }
    }

    pub fn assign(v: Var, e: Expr) -> Action {
        match e.get() {
            ActualExpr::Var(v2) if &v == v2 => Action::one(),
            _ => Action(ACTION.mk(ActualAction::Assign(v, e))),
        }
    }
}

impl From<Predicate> for Action {
    fn from(p: Predicate) -> Self {
        Action::predicate(p)
    }
}

pub trait Semiring {
    fn zero() -> Self;

    fn one() -> Self;

    fn par<T>(e1: T, e2: T) -> Self
    where
        T: Into<Self>,
        Self: Sized;

    fn seq<T>(e1: T, e2: T) -> Self
    where
        T: Into<Self>,
        Self: Sized;
}

impl Semiring for Predicate {
    fn one() -> Predicate {
        Predicate(PREDICATE.mk(ActualPredicate::One))
    }

    fn zero() -> Predicate {
        Predicate(PREDICATE.mk(ActualPredicate::Zero))
    }

    fn par<T>(p1: T, p2: T) -> Predicate
    where
        T: Into<Predicate>,
    {
        let p1 = p1.into();
        let p2 = p2.into();

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

    fn seq<T>(p1: T, p2: T) -> Predicate
    where
        T: Into<Predicate>,
    {
        let p1 = p1.into();
        let p2 = p2.into();

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
}

impl Semiring for Action {
    fn zero() -> Action {
        Action::predicate(Predicate::zero())
    }

    fn one() -> Action {
        Action::predicate(Predicate::one())
    }

    fn par<T>(a1: T, a2: T) -> Action
    where
        T: Into<Action>,
    {
        let a1 = a1.into();
        let a2 = a2.into();

        if a1.uid() == a2.uid() {
            return a1;
        }

        // 0 + a = a + 0 = a for all actions a
        if a2.is_zero() {
            return a1;
        } else if a1.is_zero() {
            return a2;
        }

        use ActualAction::*;
        match (a1.get(), a2.get()) {
            // push down predicates
            (Pred(p1), Pred(p2)) => Action::predicate(Predicate::par(p1.clone(), p2.clone())),
            // TODO: 1 + a;a* = 1 + a*;a = a*;a + 1 = a;a* + 1 = a*
            // TODO: a + pa = pa + a = a
            (_, _) => Action(ACTION.mk(Par(a1, a2))),
        }
    }

    fn seq<T>(a1: T, a2: T) -> Action
    where
        T: Into<Action>,
    {
        let a1 = a1.into();
        let a2 = a2.into();

        // 0;a = a;0 = 0 for all actions a
        if a1.is_zero() {
            return a1;
        } else if a2.is_zero() {
            return a2;
        }

        // 1;a = a;1 = a for all actions a
        if a1.is_one() {
            return a2;
        } else if a2.is_one() {
            return a1;
        }

        use ActualAction::*;
        match (a1.get(), a2.get()) {
            (Pred(p1), Pred(p2)) => Action::predicate(Predicate::seq(p1.clone(), p2.clone())),
            // a*;a* = a* for all actions a
            (Star(x1), Star(x2)) if x1 == x2 => a1,
            // TODO 2020-10-11 KMT suggest x*; x; x* == x*; x * ..?! does that really mean (x*; x)* ?
            (_, _) => Action(ACTION.mk(Seq(a1, a2))),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn smart_constructors_pone() {
        assert_eq!(
            Predicate::one(),
            Predicate::par(Predicate::one(), Predicate::zero())
        );
        assert_eq!(
            Predicate::one(),
            Predicate::par(Predicate::zero(), Predicate::one())
        );
        assert_eq!(Predicate::one(), Predicate::not(Predicate::zero()));
        assert_eq!(
            Predicate::one(),
            Predicate::not(Predicate::not(Predicate::one()))
        );
        assert_eq!(
            Predicate::one(),
            Predicate::seq(Predicate::one(), Predicate::one())
        );
    }

    #[test]
    fn smart_constructors_pzero() {
        assert_eq!(
            Predicate::zero(),
            Predicate::par(Predicate::zero(), Predicate::zero())
        );
        assert_eq!(Predicate::zero(), Predicate::not(Predicate::one()));
        assert_eq!(
            Predicate::zero(),
            Predicate::not(Predicate::not(Predicate::zero()))
        );
        assert_eq!(
            Predicate::zero(),
            Predicate::seq(Predicate::one(), Predicate::zero())
        );
        assert_eq!(
            Predicate::zero(),
            Predicate::seq(Predicate::zero(), Predicate::one())
        );
        assert_eq!(
            Predicate::zero(),
            Predicate::seq(Predicate::zero(), Predicate::zero())
        );
    }

    #[test]
    fn smart_constructors_one() {
        assert_eq!(Action::one(), Action::par(Action::one(), Action::zero()));
        assert_eq!(Action::one(), Action::par(Action::zero(), Action::one()));
        assert_eq!(Action::one(), Predicate::not(Predicate::zero()).into());
        assert_eq!(
            Action::one(),
            Predicate::not(Predicate::not(Predicate::one())).into()
        );
        assert_eq!(Action::one(), Action::seq(Action::one(), Action::one()));
    }

    #[test]
    fn smart_constructors_zero() {
        assert_eq!(Action::zero(), Action::par(Action::zero(), Action::zero()));
        assert_eq!(Action::zero(), Predicate::not(Predicate::one()).into());
        assert_eq!(
            Action::zero(),
            Predicate::not(Predicate::not(Predicate::zero())).into()
        );
        assert_eq!(Action::zero(), Action::seq(Action::one(), Action::zero()));
        assert_eq!(Action::zero(), Action::seq(Action::zero(), Action::one()));
        assert_eq!(Action::zero(), Action::seq(Action::zero(), Action::zero()));
    }
}
