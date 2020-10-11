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
    Neg(Pred<P>),
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
    pred_factory: HConsign<ActualPred<P>>,
    action_factory: HConsign<ActualAction<P, A>>,
}

impl<P: Clone + Eq + Hash, A: Clone + Eq + Hash> KAT<P, A> {
    pub fn one(&mut self) -> Pred<P> {
        self.pred_factory.mk(ActualPred::One)
    }

    pub fn zero(&mut self) -> Pred<P> {
        self.pred_factory.mk(ActualPred::Zero)
    }

    pub fn par(&mut self, p1: Pred<P>, p2: Pred<P>) -> Pred<P> {
        use ActualPred::*;

        if p1.uid() == p2.uid() {
            return p1;
        }

        match (p1.get(), p2.get()) {
            (One, _) => p1,
            (_, One) => p2,
            (_, Zero) => p1,
            (Zero, _) => p2,
            (_, _) => self.pred_factory.mk(ActualPred::Par(p1, p2)),
        }
    }
}

/*
impl<P> Pred<P> {
    

    pub fn seq(self, other: Self) -> Self {
        use Pred::*;
        match (self, other) {
            (One, p) | (p, One) => p,
            (_, p @ Zero) | (p @ Zero, _) => p,
            (p1, p2) => Pred::Seq(Box::new(p1), Box::new(p2)),
        }
    }
}
*/