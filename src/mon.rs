use std::hash::Hash;
use std::clone::Clone;
use std::cmp::{Eq, Ord, Ordering, Ordering::{Equal, Less, Greater}, max};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter, Result, Debug};
use std::ops::{Add, AddAssign, Mul, Sub, Neg, Div};
use num_traits::{Zero, Pow, ConstOne};
use num_traits::identities::One;
use super::helpers::*;

#[derive(Clone)]
#[derive(Hash)]
pub struct Monomial<X> where X : Ord + Clone {
    expo : BTreeMap<X,u8>
}

impl<X: Hash + Ord + Clone> Monomial<X> {

    fn new(expo_list : Vec<(X,u8)>) -> Monomial<X> {
        let x: Vec<(X, u8)> = expo_list.into_iter().filter(|&(_, v)| v != 0).collect();
        let new_expo: BTreeMap<X, u8> = sum_values_by_key(x);
        Monomial {expo : new_expo}
    } 

    // fn var(x : X)-> Monomial<X> {
    //     Monomial::new(vec![(x,1)])
    // }

    fn domain(&self) -> BTreeSet<X> {
        self.expo.keys().cloned().collect()
    }

    fn exp_of(&self, x : &X) -> u8 {
        let a: Option<&u8> = self.expo.get(&x);
        match a {
            Some(n) => *n,
            None => 0
        }
    }

    pub fn is_divisible_by(&self, other : &Monomial<X>) -> bool {
        let mut answer = true;
        for (x,n) in other.expo.iter() {
            if *n > self.exp_of(x) {
                answer = false;
            }
        }
        answer
    }

    pub fn lcm(&self, other : &Monomial<X>) -> Monomial<X> {
        let mut new_expo : BTreeMap<X,u8> = BTreeMap::new();
        let varset = union(self.domain(), other.domain());
        for x in varset {
            new_expo.insert(x.clone(), max(self.exp_of(&x), other.exp_of(&x)));
        }
        Monomial { expo: new_expo }
    }

    pub fn compare(&self, other : &Monomial<X>) -> Ordering {
        let vars = union(self.domain(),other.domain());
        for x in vars.into_iter().rev() {
            if self.exp_of(&x) < other.exp_of(&x) {
                return Less;
            } else if self.exp_of(&x) > other.exp_of(&x) {
                return Greater;
            } else {
                continue;
            }
        }
        return Equal;
    }
}

impl<X : Hash + Ord + Clone> PartialEq for Monomial<X> {
    fn eq(&self, other: &Self) -> bool {
        self.expo == other.expo 
    }
}

impl<X : Hash + Ord + Clone> Eq for Monomial<X> {}

impl<X : Hash + Ord + Clone> PartialOrd for  Monomial<X>{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}

// We use the revlex order

impl<X : Hash + Ord + Clone> Ord for Monomial<X> {
    fn cmp(&self, other: &Self) -> Ordering {
        let dif = find_biggest_diff_key(&self.expo, &other.expo);
       match dif {
            None => Equal,
            Some(x) => if self.exp_of(&x) < other.exp_of(&x) {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        }
    }
}

impl<X : Clone + Ord + Hash> Mul for Monomial<X> {

    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let new_expo: BTreeMap<X, u8> = merge_sum(self.expo, rhs.expo);
        Monomial {expo : new_expo}
    }
}

impl<X : Clone + Ord + Hash> Div for Monomial<X> {

    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        if !(self.is_divisible_by(&rhs)) {
            panic!("You did not check divisivility before dividing!")
        } else {
            let mut result = BTreeMap::new();
            for (x, v1) in self.expo.iter() {
                let new_val = v1 - rhs.exp_of(x);
                result.insert(x.clone(),new_val);
            }
            Monomial {expo : result}
        }
    }
}

impl<X : Clone + Ord + Hash> One for Monomial<X> {
    fn one() -> Self {
        Monomial::new(vec![])
    }
}

impl<X : Clone + Ord + Hash> Pow<u8> for Monomial<X> {
    type Output = Self;
    fn pow(self, rhs: u8) -> Self::Output {
        let new_expo: BTreeMap<X, u8> = self.expo.iter().map(|(k, v)| (k.clone(), v.clone() * rhs.clone())).collect();
        Monomial {expo : new_expo}
    }
}

impl<X : Ord + Clone + Display> Debug for Monomial<X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut to_view : String = String::new();
        for (x,n) in self.expo.iter() {
            to_view = to_view + &x.to_string() + "^" + &n.to_string() + " ";
        }
        if !(self.expo.is_empty()) {
            to_view = String::from("( ") + &to_view + ")";
        } else {
            to_view = to_view + "1";
        }
        write!(f,"{}",to_view)
    }
}

impl<X : Ord + Clone + Display> Display for Monomial<X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut to_view : String = String::new();
        for (x,n) in self.expo.iter() {
            to_view = to_view + &x.to_string() + "^" + &n.to_string() + " ";
        }
        if !(self.expo.is_empty()) {
            to_view = String::from("( ") + &to_view + ")";
        } else {
            to_view = to_view + "1";
        }
        write!(f,"{}",to_view)
    }
}

#[derive(Clone)]
#[derive(Hash)]
pub struct Polynomial<F,X>
where
  X : Hash + Ord + Clone,
{
    coeff : BTreeMap<Monomial<X>,F>
}

impl<F : AddAssign + Default + Eq + Zero + ConstOne + Clone, X : Hash + Ord + Clone> Polynomial<F,X> {
    fn new(coeff_list : Vec<(Monomial<X>, F)>) -> Polynomial<F,X> {
        let new_coeff: BTreeMap<Monomial<X>, F> = sum_values_by_key(coeff_list);
        Polynomial {coeff : new_coeff}
    }

    pub fn coeff_of(&self, p : &Monomial<X>) -> F {
        let a: Option<&F> = self.coeff.get(p);
        match a {
            Some(c) => c.clone(),
            None => F::zero()
        }
    }

    pub fn var(x : X)-> Polynomial<F,X> {
        Polynomial::new(vec![(Monomial::new(vec![(x,1)]),F::ONE.clone())])
    }

    pub fn constant(c : F) -> Polynomial<F,X> {
        Polynomial::new(vec![(Monomial::one(),c)])
    }

    pub fn square(&self) -> Polynomial<F,X> {
        self.clone() * self.clone()
    }

    fn from_mon(p : Monomial<X>) -> Polynomial<F,X> {
        Polynomial { coeff: BTreeMap::from([(p,F::one())]) }
    }

    pub fn domain(&self) -> BTreeSet<X> {
        let mut answer : BTreeSet<X> = BTreeSet::new();
        for (p,_r) in self.coeff.iter() {
            for x in p.domain() {
                if !(answer.contains(&x)) {
                    answer.insert(x);
                }
            }
        }
        answer
    }

    pub fn leading_mon(&self) -> Monomial<X> {
        let mut answer = Monomial::one();
        for (p,_c) in self.coeff.iter() {
            if answer.compare(&p) == Less {
                answer = p.clone();
            }
        }
        answer
    }

    pub fn leading_coeff(&self) -> F {
        let lm = self.leading_mon();
        self.coeff_of(&lm)
    }

    pub fn leading_term(&self) -> Polynomial<F,X> {
        let lm = self.leading_mon();
        let lc = self.coeff_of(&lm);
        Polynomial::new(vec![(lm,lc)])
    }

    pub fn is_reducible_by(&self, other : &Polynomial<F,X>) -> bool {
        if self.is_zero() || other.is_zero() {
            false
        } else if other.domain().is_subset(&self.domain()) {
            if self.leading_mon().is_divisible_by(&other.leading_mon()) {
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// One top-reduction step: if `self` is reducible by `other`, cancel the
    /// leading term of `self` with the multiple (LT(self) / LT(other)) * other.
    pub fn reduce_by(self, other : &Polynomial<F,X>) -> Polynomial<F,X>
    where
      F : Neg<Output = F> + Div<Output = F>
    {
        if  self.is_reducible_by(other) {
            let coeff = self.leading_coeff() / other.leading_coeff();
            let quotient: Polynomial<F,X> = Polynomial::new(vec![(self.leading_mon() / other.leading_mon(), coeff)]);
            self - quotient * other.clone()
        } else {
            self
        }
    }

    pub fn is_reduced(&self, base : &[Polynomial<F,X>], support : &BTreeSet<X>) -> bool
    where
      F : Display,
      X : Display
    {
        let mut answer = true;
        for g in base {
            if self.is_reducible_by(&g) {
                answer = false;
            }
        }
        answer
    }

    pub fn syzygy(self, other : &Polynomial<F,X>) -> Polynomial<F,X>
    where
      F : Div<Output = F> + Neg<Output = F> + Sub
    {
        let l = self.leading_mon().lcm(&other.leading_mon());
        let a = l.clone() / self.leading_mon();
        let b = l / other.leading_mon();
        let a2 = Polynomial::new(vec![(a,F::one()/self.leading_coeff())]);
        let f = a2 * self;
        let b2 = Polynomial::new(vec![(b,F::one()/other.leading_coeff())]);
        let g = b2 * other.clone();
        f - g
    }

    /// Applies top-reduction steps by the `reducers` until none applies, that is,
    /// until a whole pass over the reducers leaves the polynomial unchanged.
    /// The leading monomial of the result is not divisible by the leading
    /// monomial of any non-zero reducer.
    pub fn remainder(self, reducers : &[Polynomial<F,X>]) -> Polynomial<F,X>
    where
      F : Neg<Output = F> + Div<Output = F>
    {
        let mut post = self;
        loop {
            let pre = post.clone();
            for reducer in reducers.iter() {
                post = post.reduce_by(reducer);
            }
            if post == pre {
                return post;
            }
        }
    }
}

impl<F : PartialEq, X : Hash + Ord + Clone> PartialEq for Polynomial<F,X> {
    fn eq(&self, other: &Self) -> bool {
        self.coeff == other.coeff
    }
}

impl<F : PartialEq, X : Hash + Ord + Clone> Eq for Polynomial<F,X> {}

impl<F : AddAssign + Default + Zero, X : Clone + Ord + Hash> Add for Polynomial<F,X> {

    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let new_coeff: BTreeMap<Monomial<X>, F> = merge_sum(self.coeff, rhs.coeff);
        Polynomial { coeff : new_coeff}
    }
}

impl<F : Default + AddAssign + Zero, X : Clone + Ord + Hash> Zero for Polynomial<F,X> {

    fn zero() -> Self {
        Polynomial { coeff : BTreeMap::new()}
    }

    fn is_zero(&self) -> bool {
        self.coeff.len() == 0
    }
}

impl<F : AddAssign + Default + Mul<Output = F> + Clone + Zero, X : Clone + Ord + Hash> Mul for Polynomial<F,X>
{

    type Output = Self;

    fn mul(self : Self, other : Self) -> Self {
        let mut result: Polynomial<F,X> = Polynomial::zero();
        for (p1,r1) in self.coeff.iter() {
            for (p2, r2) in other.coeff.iter() {
                result.coeff.entry(p1.clone()*p2.clone()).or_default().add_assign(r1.clone() * r2.clone());
            }
        }
        result
    }
}

impl<F : One + AddAssign + Default + Clone + ConstOne + Zero, X : Hash + Clone + Ord> One for Polynomial<F,X>{

    fn one() -> Self {
        let mut new_coeff : BTreeMap<Monomial<X>,F> = BTreeMap::new();
        new_coeff.insert(Monomial::one(), F::one());
        Polynomial { coeff: new_coeff }
    }
}

impl<F : Clone + AddAssign + Default + One + Eq + Zero + ConstOne,X : Clone + Ord + Hash> Pow<u8> for Polynomial<F,X> {
    type Output = Self;

    fn pow(self, rhs: u8) -> Self::Output {
        if rhs == 0 {
            Polynomial::one()
        } else if rhs == 1 {
            self
        } else {
            let maybe_answer = self.clone().pow(rhs/2);
            if rhs % 2 == 0 {
                maybe_answer.square()
            } else {
                maybe_answer.square() * self
            }          
        }
    }
}

impl<F : Display, X : Hash + Ord + Clone + Display> Display for Polynomial<F,X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut to_view : String = String::new();
        for (p,c) in self.coeff.iter() {
            if *p == Monomial::one() {
                to_view = to_view + "+ " + &c.to_string() + " ";
            } else {
                to_view = to_view + "+ " + &c.to_string() + "." + &p.to_string() + " ";
            }
        }
        
        if self.coeff.is_empty() {
            to_view = String::from("0");
        }

        write!(f,"{}",to_view)
    }
}

impl<F : Display, X : Hash + Ord + Clone + Display> Debug for Polynomial<F,X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut to_view : String = String::new();
        for (p,c) in self.coeff.iter() {
            if *p == Monomial::one() {
                to_view = to_view + "+ " + &c.to_string() + " ";
            } else {
                to_view = to_view + "+ " + &c.to_string() + "." + &p.to_string() + " ";
            }
        }
        
        if self.coeff.is_empty() {
            to_view = String::from("0");
        }

        write!(f,"{}",to_view)
    }
}

impl<F : Neg<Output = F> + Clone, X : Hash + Ord + Clone> Neg for Polynomial<F,X> {

    type Output = Self;

    fn neg(self) -> Self {
    let new_coeff = self.coeff.into_iter()
        .map(|(k, v)| (k, v.neg()))
        .collect();
    Polynomial { coeff: new_coeff }
    }
}

impl<F : Neg<Output = F> + Clone + AddAssign + Default + Zero, X : Hash + Ord + Clone> Sub for Polynomial<F,X> {
    type Output = Self;

    fn sub(self,other: Self) -> Self {
        self + other.neg()
    }
}

impl<F : Neg<Output = F> + Clone + AddAssign + Default + Zero + Ord + ConstOne, X : Hash + Ord + Clone> PartialOrd for Polynomial<F,X> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let dif = find_biggest_diff_key(&self.coeff, &other.coeff);
       match dif {
            None => Some(Equal),
            Some(x) => if self.coeff_of(&x) < other.coeff_of(&x) {
                Some(Less)
            } else {
                Some(Greater)
            }
        }
    }
}

impl<F : Neg<Output = F> + Clone + AddAssign + Default + Zero + Ord + ConstOne, X : Hash + Ord + Clone> Ord for Polynomial<F,X> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.partial_cmp(other) {
            Some(a) => a,
            None => panic!("The ordering is supposed to be total")
        }
    }
}

// impl<F : Clone, X:AtomsWithOrd + Hash + Clone> SetWithAtoms<X> for Polynomial<F,X> {

//     fn apply_PAut(&self, paut : PartialAut<X>) -> Self
//         where
//             Self : Sized {
//                 if self.domain().size


//                 return self.clone();
//     }
// }
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bits::F2;
    use num_rational::Rational64 as Q;

    type PQ = Polynomial<Q, String>;
    type P2 = Polynomial<F2, String>;

    fn qv(name : &str) -> PQ { Polynomial::var(name.to_string()) }
    fn qc(num : i64, den : i64) -> PQ { Polynomial::constant(Q::new(num, den)) }
    fn v2(name : &str) -> P2 { Polynomial::var(name.to_string()) }

    #[test]
    fn reduce_by_uses_leading_coefficients() {
        let x = qv("x");
        // x reduced by 2x is 0.
        let two_x = qc(2, 1) * x.clone();
        assert!(x.clone().reduce_by(&two_x).is_zero());
        // 3x^2 + 1 reduced by 2x + 1 is -3/2 x + 1.
        let f = qc(3, 1) * x.clone() * x.clone() + qc(1, 1);
        let g = qc(2, 1) * x.clone() + qc(1, 1);
        assert_eq!(f.reduce_by(&g), qc(-3, 2) * x.clone() + qc(1, 1));
    }

    #[test]
    fn remainder_reduces_until_no_reducer_applies() {
        let (x, y, z) = (v2("x"), v2("y"), v2("z"));
        let g = y.clone() + x.clone();
        let reducers = vec![g.clone(), z.clone()];
        // y^2 + x -> xy + x -> x^2 + x (the last reducer z never applies).
        let r = (y.clone() * y.clone() + x.clone()).remainder(&reducers);
        assert_eq!(r, x.clone() * x.clone() + x.clone());
        assert!(reducers.iter().all(|h| !r.is_reducible_by(h)));
    }

    #[test]
    fn remainder_with_no_reducers() {
        let x = v2("x");
        assert_eq!(x.clone().remainder(&[]), x);
    }
}
