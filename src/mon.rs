use std::hash::Hash;
use std::clone::Clone;
use std::cmp::{Eq, Ord, Ordering, Ordering::{Equal, Less, Greater}, max};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter, Result, Debug};
use std::ops::{Add, AddAssign, Mul, Sub, Neg, Div};
use num_traits::{Zero, Pow, ConstOne};
use num_traits::identities::One;
use super::helpers::*;

/// The type of exponents of variables in monomials.
pub type Exponent = u32;

/// A monomial, stored as a map from variables to their (non-zero) exponents.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Monomial<X> where X : Ord + Clone {
    expo : BTreeMap<X,Exponent>
}

impl<X: Hash + Ord + Clone> Monomial<X> {

    fn new(expo_list : Vec<(X,Exponent)>) -> Monomial<X> {
        let x: Vec<(X, Exponent)> = expo_list.into_iter().filter(|&(_, v)| v != 0).collect();
        let new_expo: BTreeMap<X, Exponent> = sum_values_by_key(x);
        Monomial {expo : new_expo}
    } 

    // fn var(x : X)-> Monomial<X> {
    //     Monomial::new(vec![(x,1)])
    // }

    fn domain(&self) -> BTreeSet<X> {
        self.expo.keys().cloned().collect()
    }

    fn exp_of(&self, x : &X) -> Exponent {
        let a: Option<&Exponent> = self.expo.get(x);
        match a {
            Some(n) => *n,
            None => 0
        }
    }

    /// The monomial obtained by replacing every variable x by f(x).
    pub fn rename_variables(&self, f : impl Fn(&X) -> X) -> Monomial<X> {
        self.map_variables(f)
    }

    /// The monomial obtained by replacing every variable x by f(x), where the new
    /// variables may have another type. If f is not injective, the exponents of
    /// the variables with the same image are added.
    pub fn map_variables<Y : Hash + Ord + Clone>(&self, f : impl Fn(&X) -> Y) -> Monomial<Y> {
        Monomial::new(self.expo.iter().map(|(x, e)| (f(x), *e)).collect())
    }

    /// The variables of the monomial with their (non-zero) exponents, in
    /// increasing order of the variables.
    pub fn exponents(&self) -> impl Iterator<Item = (&X, Exponent)> {
        self.expo.iter().map(|(x, e)| (x, *e))
    }

    /// The total degree: the sum of the exponents.
    pub fn degree(&self) -> Exponent {
        self.expo.values().sum()
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
        let mut new_expo : BTreeMap<X,Exponent> = BTreeMap::new();
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
        Equal
    }
}

impl<X : Hash + Ord + Clone> PartialOrd for  Monomial<X>{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// Monomials are compared lexicographically, with the largest variable as the most
// significant one: the exponents are compared at the largest variable where they
// differ. For example, x^5 < y when x < y.

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
        let mut new_expo: BTreeMap<X, Exponent> = self.expo;
        for (x, e) in rhs.expo {
            let entry = new_expo.entry(x).or_insert(0);
            *entry = entry.checked_add(e).expect("exponent overflow in monomial multiplication");
        }
        new_expo.retain(|_, e| *e != 0);
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
                // Keep the representation normalised: no zero exponents.
                if new_val != 0 {
                    result.insert(x.clone(),new_val);
                }
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

impl<X : Clone + Ord + Hash> Pow<Exponent> for Monomial<X> {
    type Output = Self;
    fn pow(self, rhs: Exponent) -> Self::Output {
        let new_expo: BTreeMap<X, Exponent> = self.expo.into_iter()
            .map(|(k, v)| (k, v.checked_mul(rhs).expect("exponent overflow in monomial power")))
            .filter(|(_, v)| *v != 0)
            .collect();
        Monomial {expo : new_expo}
    }
}

impl<X : Clone + Ord + Hash> Pow<u8> for Monomial<X> {
    type Output = Self;
    fn pow(self, rhs: u8) -> Self::Output {
        self.pow(Exponent::from(rhs))
    }
}

impl<X : Ord + Clone + Display> Debug for Monomial<X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self)
    }
}

// Example: x y^2 is displayed as "( x^1 y^2 )", and the monomial 1 as "1".
impl<X : Ord + Clone + Display> Display for Monomial<X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.expo.is_empty() {
            return write!(f, "1");
        }
        write!(f, "( ")?;
        for (x, n) in self.expo.iter() {
            write!(f, "{}^{} ", x, n)?;
        }
        write!(f, ")")
    }
}

/// A polynomial, stored as a map from monomials to their (non-zero) coefficients.
#[derive(Clone, Hash, PartialEq, Eq)]
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

    /// The monomials of the polynomial, in increasing order.
    pub fn monomials(&self) -> impl DoubleEndedIterator<Item = &Monomial<X>> {
        self.coeff.keys()
    }

    /// The monomial `m` as a polynomial, with coefficient 1.
    pub fn from_monomial(m : Monomial<X>) -> Polynomial<F,X> {
        Polynomial::new(vec![(m, F::one())])
    }

    pub fn square(&self) -> Polynomial<F,X> {
        self.clone() * self.clone()
    }

    /// The polynomial obtained by replacing every variable x by f(x).
    pub fn rename_variables(&self, f : impl Fn(&X) -> X) -> Polynomial<F,X> {
        self.map_variables(f)
    }

    /// The polynomial obtained by replacing every variable x by f(x), where the
    /// new variables may have another type. This is a ring morphism: if f is not
    /// injective, the coefficients of the monomials with the same image are added.
    pub fn map_variables<Y : Hash + Ord + Clone>(&self, f : impl Fn(&X) -> Y) -> Polynomial<F,Y> {
        Polynomial::new(self.coeff.iter().map(|(m, c)| (m.map_variables(&f), c.clone())).collect())
    }

    /// The set of variables that occur in the polynomial.
    pub fn domain(&self) -> BTreeSet<X> {
        self.coeff.keys().flat_map(|p| p.domain()).collect()
    }

    /// The leading monomial (1 for the zero polynomial). The coefficient map is
    /// sorted by the monomial order, so this is its last key.
    pub fn leading_mon(&self) -> Monomial<X> {
        match self.coeff.keys().next_back() {
            Some(p) => p.clone(),
            None => Monomial::one(),
        }
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

    /// Whether `self` is top-reducible by `other`: both are non-zero and the
    /// leading monomial of `other` divides the leading monomial of `self`.
    pub fn is_reducible_by(&self, other : &Polynomial<F,X>) -> bool {
        !self.is_zero()
            && !other.is_zero()
            && self.leading_mon().is_divisible_by(&other.leading_mon())
    }

    /// One top-reduction step: if `self` is reducible by `other`, cancel the
    /// leading term of `self` with the multiple (LT(self) / LT(other)) * other.
    pub fn reduce_by(self, other : &Polynomial<F,X>) -> Polynomial<F,X>
    where
      F : Neg<Output = F> + Div<Output = F>
    {
        if  self.is_reducible_by(other) {
            crate::counters::count_reduction();
            let coeff = self.leading_coeff() / other.leading_coeff();
            let quotient: Polynomial<F,X> = Polynomial::new(vec![(self.leading_mon() / other.leading_mon(), coeff)]);
            self - quotient * other.clone()
        } else {
            self
        }
    }

    /// Whether `self` is not top-reducible by any polynomial in `base`.
    pub fn is_reduced(&self, base : &[Polynomial<F,X>]) -> bool {
        !base.iter().any(|g| self.is_reducible_by(g))
    }

    pub fn syzygy(self, other : &Polynomial<F,X>) -> Polynomial<F,X>
    where
      F : Div<Output = F> + Neg<Output = F> + Sub
    {
        crate::counters::count_s_polynomial();
        let l = self.leading_mon().lcm(&other.leading_mon());
        let a = l.clone() / self.leading_mon();
        let b = l / other.leading_mon();
        let a2 = Polynomial::new(vec![(a,F::one()/self.leading_coeff())]);
        let f = a2 * self;
        let b2 = Polynomial::new(vec![(b,F::one()/other.leading_coeff())]);
        let g = b2 * other.clone();
        f - g
    }

    /// Cancels the term of `self` at the monomial `m` with a multiple of `other`.
    /// The leading monomial of `other` must divide `m`.
    pub fn reduce_term_by(self, m : &Monomial<X>, other : &Polynomial<F,X>) -> Polynomial<F,X>
    where
      F : Neg<Output = F> + Div<Output = F>
    {
        crate::counters::count_reduction();
        let coeff = self.coeff_of(m) / other.leading_coeff();
        let quotient : Polynomial<F,X> = Polynomial::new(vec![(m.clone() / other.leading_mon(), coeff)]);
        self - quotient * other.clone()
    }

    /// The normal form of `self` with respect to `reducers`: the remainder of the
    /// division algorithm. No monomial of the result is divisible by the leading
    /// monomial of a non-zero reducer.
    pub fn normal_form(self, reducers : &[Polynomial<F,X>]) -> Polynomial<F,X>
    where
      F : Neg<Output = F> + Div<Output = F>
    {
        let mut p = self;
        let mut r : Polynomial<F,X> = Polynomial::zero();
        while let Some(m) = p.coeff.keys().next_back().cloned() {
            match reducers.iter().find(|g| !g.is_zero() && m.is_divisible_by(&g.leading_mon())) {
                Some(g) => p = p.reduce_by(g),
                None => {
                    // The leading term of p is irreducible: move it to the remainder.
                    let (m, c) = p.coeff.pop_last().unwrap();
                    r.coeff.insert(m, c);
                }
            }
        }
        r
    }

    /// The polynomial divided by its leading coefficient (zero stays zero).
    pub fn monic(self) -> Polynomial<F,X>
    where
      F : Div<Output = F>
    {
        if self.is_zero() {
            self
        } else {
            let c = F::one() / self.leading_coeff();
            Polynomial::constant(c) * self
        }
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
        self.coeff.is_empty()
    }
}

impl<F : AddAssign + Default + Mul<Output = F> + Clone + Zero, X : Clone + Ord + Hash> Mul for Polynomial<F,X>
{

    type Output = Self;

    fn mul(self, other : Self) -> Self {
        let mut result: Polynomial<F,X> = Polynomial::zero();
        for (p1,r1) in self.coeff.iter() {
            for (p2, r2) in other.coeff.iter() {
                result.coeff.entry(p1.clone()*p2.clone()).or_default().add_assign(r1.clone() * r2.clone());
            }
        }
        // Terms may cancel, e.g. (x + y)(x + y) = x^2 + y^2 over F2.
        result.coeff.retain(|_, c| !c.is_zero());
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
        self.pow(Exponent::from(rhs))
    }
}

impl<F : Clone + AddAssign + Default + One + Eq + Zero + ConstOne,X : Clone + Ord + Hash> Pow<Exponent> for Polynomial<F,X> {
    type Output = Self;

    fn pow(self, rhs: Exponent) -> Self::Output {
        if rhs == 0 {
            Polynomial::one()
        } else if rhs == 1 {
            self
        } else {
            let maybe_answer = self.clone().pow(rhs/2);
            if rhs.is_multiple_of(2) {
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

    // Subtraction is addition of the negation.
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self,other: Self) -> Self {
        self + other.neg()
    }
}

impl<F : Neg<Output = F> + Clone + AddAssign + Default + Zero + Ord + ConstOne, X : Hash + Ord + Clone> PartialOrd for Polynomial<F,X> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// A total order on polynomials (used to store them in sorted sets): compare the
// coefficients of the largest monomial at which the two polynomials differ.
impl<F : Neg<Output = F> + Clone + AddAssign + Default + Zero + Ord + ConstOne, X : Hash + Ord + Clone> Ord for Polynomial<F,X> {
    fn cmp(&self, other: &Self) -> Ordering {
        match find_biggest_diff_key(&self.coeff, &other.coeff) {
            None => Equal,
            Some(x) => if self.coeff_of(&x) < other.coeff_of(&x) {
                Less
            } else {
                Greater
            }
        }
    }
}

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
    fn products_have_no_zero_coefficients() {
        let (x, y) = (v2("x"), v2("y"));
        let p = (x.clone() + y.clone()) * (x.clone() + y.clone());
        assert_eq!(p, x.clone() * x.clone() + y.clone() * y.clone());
        let q = (qv("x") + qv("y")) * (qv("x") - qv("y"));
        assert_eq!(q, qv("x") * qv("x") - qv("y") * qv("y"));
        // (x + 1)(x - 1) - (x^2 - 1) is the zero polynomial.
        let d = (qv("x") + qc(1, 1)) * (qv("x") - qc(1, 1)) - (qv("x") * qv("x") - qc(1, 1));
        assert!(d.is_zero());
    }

    #[test]
    fn reducibility_only_depends_on_leading_monomials() {
        let (x, y) = (v2("x"), v2("y"));
        let f = y.clone() * y.clone();
        let g = y.clone() + x.clone();
        // LM(y + x) = y divides LM(y^2) = y^2, although x does not occur in y^2.
        assert!(f.is_reducible_by(&g));
        assert_eq!(f.reduce_by(&g), x.clone() * y.clone());
        assert!(!x.is_reducible_by(&g));
        assert!(!x.is_reducible_by(&P2::zero()));
    }

    #[test]
    fn monomials_stay_normalised() {
        let x = v2("x");
        let y = v2("y");
        // x^2 y / x^2 = y, with no zero exponent left for x.
        let m = (x.clone() * x.clone() * y.clone()).leading_mon() / (x.clone() * x.clone()).leading_mon();
        assert_eq!(m, y.leading_mon());
        assert_eq!(x.leading_mon().pow(0u8), Monomial::one());
    }

    #[test]
    fn exponents_above_255() {
        let x = v2("x");
        let p = x.clone().pow(200u8) * x.clone().pow(200u8);
        assert_eq!(p, x.clone().pow(400 as Exponent));
        assert!(p != x);
    }

    #[test]
    fn leading_monomial_is_the_maximum() {
        let (x, y, z) = (v2("x"), v2("y"), v2("z"));
        let p = x.clone().pow(5u8) + y.clone() * z.clone() + y.clone().pow(3u8) + z.clone() + P2::one();
        let by_compare = p.coeff.keys().cloned()
            .fold(Monomial::one(), |best, m| if best.compare(&m) == Less { m } else { best });
        assert_eq!(p.leading_mon(), by_compare);
        assert_eq!(p.leading_mon(), (y.clone() * z.clone()).leading_mon());
    }

    #[test]
    fn renaming_variables() {
        let (x, y, z) = (v2("x"), v2("y"), v2("z"));
        let f = x.clone() * x.clone() * z.clone() + y.clone();
        let rename = |v : &String| if v == "z" { "w".to_string() } else { v.clone() };
        assert_eq!(f.rename_variables(rename), x.clone() * x.clone() * v2("w") + y.clone());
        // A renaming that is not injective merges monomials: x + y becomes 2x = 0 over F2.
        let merge = |_ : &String| "x".to_string();
        assert!((x.clone() + y.clone()).rename_variables(merge).is_zero());
    }

    #[test]
    fn remainder_with_no_reducers() {
        let x = v2("x");
        assert_eq!(x.clone().remainder(&[]), x);
    }
}
