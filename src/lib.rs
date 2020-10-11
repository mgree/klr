#[macro_use]
extern crate hashconsing;
use std::hash::Hash;
use hashconsing::{ HConsed, HashConsign, HConsign } ;

use std::fmt::Debug;

pub type Pred<P> = HConsed<ActualPred<P>>;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualPred<P> {
    One,
    Zero,
    Par(Pred<P>, Pred<P>),
    Seq(Pred<P>, Pred<P>),
    Not(Pred<P>),
    User(P),
}

pub type Action<P, A> = HConsed<ActualAction<P, A>>;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ActualAction<P, A> {
    Pred(Pred<P>),
    Par(Action<P, A>, Action<P, A>),
    Seq(Action<P, A>, Action<P, A>),
    Star(Action<P, A>),
    User(A),    
}

pub struct KAT<P: Clone + Eq + Hash, A: Clone + Eq + Hash> {
    pred: HConsign<ActualPred<P>>,
    action: HConsign<ActualAction<P, A>>,
}

impl<P: Clone + Eq + Hash, A: Clone + Eq + Hash> KAT<P, A> {
    pub fn pone(&mut self) -> Pred<P> {
        self.pred.mk(ActualPred::One)
    }

    pub fn pzero(&mut self) -> Pred<P> {
        self.pred.mk(ActualPred::Zero)
    }

    pub fn ppar(&mut self, p1: Pred<P>, p2: Pred<P>) -> Pred<P> {
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
            (_, _) => self.pred.mk(ActualPred::Par(p1, p2)),
        }
    }

    pub fn pseq(&mut self, p1: Pred<P>, p2: Pred<P>) -> Pred<P> {
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
                let p12_p2 = self.pseq(p12.clone(), p2);
                self.pseq(p11.clone(),p12_p2)
            }
            (_, _) => self.pred.mk(ActualPred::Seq(p1, p2)),
        }
    }

    pub fn pnot(&mut self, p: Pred<P>) -> Pred<P> {
        use ActualPred::*;

        match p.get() {
            One => self.pzero(),
            Zero => self.pone(),
            Not(p) => p.clone(),
            _ => self.pred.mk(ActualPred::Not(p)),
        }
    }

    pub fn puser(&mut self, p: P) -> Pred<P> {
        self.pred.mk(ActualPred::User(p))
    }
}
