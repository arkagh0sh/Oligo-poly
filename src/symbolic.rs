//! Symbolic atoms: the elements of a homogeneous structure that is only given
//! by its theory.
//!
//! A [`SymbolicTheory`] gives a signature with the order `<`, and axioms. The
//! structure M of the atoms is the homogeneous structure whose finite
//! substructures are the finite models of the axioms in which `<` is a linear
//! order. In M, the orbit of a tuple is determined by the isomorphism type of
//! the substructure that it generates, with the tuple marked in it.
//!
//! So a [`SymbolicAtom`] is an element of a finite structure: it holds a shared
//! pointer to the structure, whose elements are numbered in increasing order.
//! The orbit tests compare finite structures, and new orbits, such as the
//! orbits of pairs, are found by a search for finite models with a SAT solver.
//!
//! The public functions are equivariant:
//! - [`orbit_of`] gives the orbit that a description defines, or an error if
//!   the description defines no orbit or several orbits;
//! - [`describe`] gives a description that defines an orbit of tuples;
//! - [`diagram`] gives the formula of such a description, for any structure.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::OnceLock;
use varisat::{ExtendFormula, Lit, Solver};
use crate::atoms::{AtomsWithOrd, HomogeneousStructure, Orbit, SetPairOrbit, Structure};
use crate::elements_with_atoms::{ElementsWithAtoms, PartialAut};
use crate::logic::{flatten, Axiom, Description, Formula, Signature, Term, Theory, LINEAR_ORDER, TREE_AXIOMS};

/// A theory of ordered atoms, named by a type.
///
/// The implementation declares, and nothing checks, that:
/// - the signature has the binary relation `<` and no constants;
/// - the finite models of the axioms in which `<` is a linear order are the
///   finite substructures of a homogeneous structure;
/// - in this structure, k elements generate a substructure with at most
///   `generated_size_bound(k)` elements.
pub trait SymbolicTheory : 'static {
    fn theory() -> &'static Theory;
    fn generated_size_bound(k : usize) -> usize;
}

/// The dense linear order (Q, <).
pub struct DenseOrder;

impl SymbolicTheory for DenseOrder {
    fn theory() -> &'static Theory {
        static THEORY : OnceLock<Theory> = OnceLock::new();
        THEORY.get_or_init(|| Theory::new(Signature::new(&[("<", 2)], &[]), &LINEAR_ORDER).unwrap())
    }

    /// Without functions, k elements generate a substructure with k elements.
    fn generated_size_bound(k : usize) -> usize {
        k
    }
}

/// The dense meet-tree with a lexicographic order, as the atoms `Tree`.
pub struct MeetTree;

impl SymbolicTheory for MeetTree {
    fn theory() -> &'static Theory {
        static THEORY : OnceLock<Theory> = OnceLock::new();
        THEORY.get_or_init(|| {
            let signature = Signature::new(&[("<", 2), ("le", 2)], &[("meet", 2)]);
            Theory::new(signature, &[&LINEAR_ORDER[..], &TREE_AXIOMS[..]].concat()).unwrap()
        })
    }

    /// The meets of k >= 1 points of a tree add at most k - 1 points.
    fn generated_size_bound(k : usize) -> usize {
        (2 * k).saturating_sub(1)
    }
}

/// A finite structure whose elements 0, ..., size - 1 are numbered in
/// increasing order. The tables of the relations (except `<`, which is the
/// order of the numbers, and has an empty table) and of the functions are
/// indexed by the tuples of arguments, read in base `size`. Every structure has
/// its own identifier.
struct FiniteStructure {
    id : u64,
    size : usize,
    relations : Vec<Vec<bool>>,
    functions : Vec<Vec<usize>>,
}

impl FiniteStructure {
    fn position(&self, args : &[usize]) -> usize {
        args.iter().fold(0, |p, &a| p * self.size + a)
    }
}

thread_local! {
    static NEXT_ID : Cell<u64> = const { Cell::new(0) };
}

fn fresh_id() -> u64 {
    NEXT_ID.with(|next| {
        let id = next.get();
        next.set(id + 1);
        id
    })
}

/// A symbolic atom: an element of a finite substructure of the structure of
/// the theory `T`. Atoms are only related to atoms of the same finite
/// structure. The algorithms only combine elements with atoms after moving
/// them into a common structure, by partial automorphisms.
pub struct SymbolicAtom<T> {
    structure : Rc<FiniteStructure>,
    index : usize,
    theory : PhantomData<fn() -> T>,
}

impl<T> SymbolicAtom<T> {
    fn new(structure : &Rc<FiniteStructure>, index : usize) -> Self {
        SymbolicAtom { structure : structure.clone(), index, theory : PhantomData }
    }

    fn key(&self) -> (u64, usize) {
        (self.structure.id, self.index)
    }
}

impl<T> Clone for SymbolicAtom<T> {
    fn clone(&self) -> Self {
        SymbolicAtom::new(&self.structure, self.index)
    }
}

impl<T> PartialEq for SymbolicAtom<T> {
    fn eq(&self, other : &Self) -> bool {
        self.key() == other.key()
    }
}

impl<T> Eq for SymbolicAtom<T> {}

impl<T> Hash for SymbolicAtom<T> {
    fn hash<H : Hasher>(&self, state : &mut H) {
        self.key().hash(state)
    }
}

/// Inside a structure, the order of the atoms is the order `<` of the theory.
/// Atoms of different structures are ordered by their structures.
impl<T> PartialOrd for SymbolicAtom<T> {
    fn partial_cmp(&self, other : &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for SymbolicAtom<T> {
    fn cmp(&self, other : &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

impl<T> Debug for SymbolicAtom<T> {
    fn fmt(&self, f : &mut Formatter<'_>) -> fmt::Result {
        write!(f, "a{}.{}", self.structure.id, self.index)
    }
}

impl<T> Display for SymbolicAtom<T> {
    fn fmt(&self, f : &mut Formatter<'_>) -> fmt::Result {
        write!(f, "a{}", self.index)
    }
}

/// The structure of `args`, which must all be atoms of the same structure.
fn common<T>(args : &[SymbolicAtom<T>]) -> &FiniteStructure {
    let s = &args.first().expect("a symbolic theory has no constants").structure;
    debug_assert!(args.iter().all(|a| Rc::ptr_eq(&a.structure, s)), "atoms of different structures");
    s
}

fn indices<T>(args : &[SymbolicAtom<T>]) -> Vec<usize> {
    args.iter().map(|a| a.index).collect()
}

/// The number of the relation `<` in the signature of `T`.
fn order<T : SymbolicTheory>() -> usize {
    T::theory().signature.relation("<").expect("a symbolic theory must have the order <")
}

impl<T : SymbolicTheory> Structure for SymbolicAtom<T> {
    fn theory() -> &'static Theory {
        T::theory()
    }

    fn holds(r : usize, args : &[Self]) -> bool {
        let s = common(args);
        if r == order::<T>() {
            args[0].index < args[1].index
        } else {
            s.relations[r][s.position(&indices(args))]
        }
    }

    fn apply(f : usize, args : &[Self]) -> Self {
        let s = common(args);
        SymbolicAtom::new(&args[0].structure, s.functions[f][s.position(&indices(args))])
    }
}

/// The declaration of the theory: its structure is homogeneous.
impl<T : SymbolicTheory> HomogeneousStructure for SymbolicAtom<T> {}

impl<T : SymbolicTheory> AtomsWithOrd for SymbolicAtom<T> {
    /// Let s and t list `first` and `second` in increasing order. The orbits of
    /// pairs (S', T') in the product are the orbits of the tuples (s', t') with
    /// s' in the orbit of s and t' in the orbit of t. These are the finite
    /// models generated by a tuple (s', t') that satisfies the diagrams of s
    /// and t, up to isomorphism.
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> Vec<SetPairOrbit<Self>> {
        let s : Vec<Self> = first.iter().cloned().collect();
        let t : Vec<Self> = second.iter().cloned().collect();
        let p = s.len();
        let shifted = diagram(&t).map_terms(&mut |term| shift(term, p));
        let formula = Formula::And(vec![diagram(&s), shifted]);
        generated_models::<T>(p + t.len(), &formula, usize::MAX)
            .into_iter()
            .map(|tuple| Orbit::new((tuple[..p].iter().cloned().collect(), tuple[p..].iter().cloned().collect())))
            .collect()
    }
}

/// An atom is an element with atoms, with support {a}.
impl<T : SymbolicTheory> ElementsWithAtoms<SymbolicAtom<T>> for SymbolicAtom<T> {
    fn support(&self) -> BTreeSet<SymbolicAtom<T>> {
        BTreeSet::from([self.clone()])
    }

    fn apply_paut(&self, paut : &PartialAut<SymbolicAtom<T>>) -> Self {
        paut.apply(self)
    }
}

/// The orbits of elements built from symbolic atoms.
pub type SymbolicOrbit<T, B> = Orbit<SymbolicAtom<T>, B>;

/// Why a description does not define an orbit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DescriptionError {
    /// No tuple of atoms satisfies the description.
    InconsistentFormula,
    /// Tuples of several orbits satisfy the description; the error gives the
    /// descriptions of two of these orbits.
    AmbiguousFormula(Box<(Description, Description)>),
}

impl Display for DescriptionError {
    fn fmt(&self, f : &mut Formatter<'_>) -> fmt::Result {
        match self {
            DescriptionError::InconsistentFormula => write!(f, "no tuple of atoms satisfies the description"),
            DescriptionError::AmbiguousFormula(..) => write!(f, "tuples of several orbits satisfy the description"),
        }
    }
}

/// The orbit of the tuples of atoms that satisfy a description, if they form
/// one orbit.
pub fn orbit_of<T : SymbolicTheory>(description : &Description)
    -> Result<SymbolicOrbit<T, Vec<SymbolicAtom<T>>>, DescriptionError> {
    let mut tuples = generated_models::<T>(description.variables.len(), &description.formula, 2);
    let named = |tuple : &[SymbolicAtom<T>]| Description { variables : description.variables.clone(), formula : diagram(tuple) };
    match tuples.len() {
        0 => Err(DescriptionError::InconsistentFormula),
        1 => Ok(Orbit::new(tuples.pop().unwrap())),
        _ => Err(DescriptionError::AmbiguousFormula(Box::new((named(&tuples[0]), named(&tuples[1]))))),
    }
}

/// A description that defines the given orbit of tuples, with the variables
/// x1, x2, ...
pub fn describe<T : SymbolicTheory>(orbit : &SymbolicOrbit<T, Vec<SymbolicAtom<T>>>) -> Description {
    orbit.evaluate(|tuple| Description {
        variables : (1..=tuple.len()).map(|i| format!("x{i}")).collect(),
        formula : diagram(tuple),
    })
}

/// A shorter description of the same orbit. The conjuncts of the description,
/// which must define one orbit, are dropped one at a time, from the last one,
/// as long as the rest still defines one orbit. The result is implied by the
/// description, so it defines the same orbit.
pub fn simplify<T : SymbolicTheory>(description : &Description) -> Description {
    let Formula::And(conjuncts) = &description.formula else {
        return description.clone();
    };
    let k = description.variables.len();
    let mut kept = conjuncts.clone();
    for i in (0..kept.len()).rev() {
        let mut candidate = kept.clone();
        candidate.remove(i);
        if generated_models::<T>(k, &Formula::And(candidate.clone()), 2).len() == 1 {
            kept = candidate;
        }
    }
    Description { variables : description.variables.clone(), formula : Formula::And(kept) }
}

/// The diagram of a tuple: a formula in the variables 0, ..., k - 1 that holds
/// at a tuple exactly when the substructures generated by the two tuples are
/// isomorphic by the map between the tuples. It names every element of the
/// generated substructure by a term, and lists the equalities between the
/// variables, the relations between the elements, and the values of the
/// functions. It only depends on the orbit of the tuple. In a homogeneous
/// structure, it defines the orbit of the tuple.
///
/// If the signature has the order `<`, which must then be a linear order,
/// only the instances t < u where no element lies between t and u are listed:
/// the others follow by transitivity, and they also say that the elements are
/// distinct.
pub fn diagram<S : Structure>(tuple : &[S]) -> Formula {
    let signature = &S::theory().signature;
    let mut elements : Vec<S> = Vec::new();
    let mut terms : Vec<Term> = Vec::new();
    let mut conjuncts = Vec::new();
    for (i, a) in tuple.iter().enumerate() {
        match elements.iter().position(|b| b == a) {
            Some(p) => conjuncts.push(Formula::Eq(Term::Var(i), terms[p].clone())),
            None => {
                elements.push(a.clone());
                terms.push(Term::Var(i));
            }
        }
    }
    // Name the elements of the generated substructure.
    loop {
        let mut new = false;
        for (f, (_, arity)) in signature.functions.iter().enumerate() {
            for args in tuples(elements.len(), *arity) {
                let value = S::apply(f, &args.iter().map(|&i| elements[i].clone()).collect::<Vec<_>>());
                if !elements.contains(&value) {
                    elements.push(value);
                    terms.push(Term::App(f, args.iter().map(|&i| terms[i].clone()).collect()));
                    new = true;
                }
            }
        }
        if !new {
            break;
        }
    }
    let n = elements.len();
    let pick = |args : &[usize]| -> Vec<S> { args.iter().map(|&i| elements[i].clone()).collect() };
    let order = signature.relation("<");
    if order.is_none() {
        for q in 0..n {
            for p in 0..q {
                conjuncts.push(Formula::negate(Formula::Eq(terms[p].clone(), terms[q].clone())));
            }
        }
    }
    for (r, (_, arity)) in signature.relations.iter().enumerate() {
        for args in tuples(n, *arity) {
            let atom = Formula::Rel(r, args.iter().map(|&i| terms[i].clone()).collect());
            let holds = S::holds(r, &pick(&args));
            if Some(r) == order {
                let between = |c : usize| S::holds(r, &pick(&[args[0], c])) && S::holds(r, &pick(&[c, args[1]]));
                if holds && !(0..n).any(between) {
                    conjuncts.push(atom);
                }
            } else {
                conjuncts.push(if holds { atom } else { Formula::negate(atom) });
            }
        }
    }
    for (f, (_, arity)) in signature.functions.iter().enumerate() {
        for args in tuples(n, *arity) {
            let value = S::apply(f, &pick(&args));
            let p = elements.iter().position(|b| *b == value).unwrap();
            let term = Term::App(f, args.iter().map(|&i| terms[i].clone()).collect());
            if terms[p] != term {
                conjuncts.push(Formula::Eq(term, terms[p].clone()));
            }
        }
    }
    Formula::And(conjuncts)
}

/// The term with every variable i replaced by i + p.
fn shift(t : &Term, p : usize) -> Term {
    match t {
        Term::Var(i) => Term::Var(i + p),
        Term::App(f, args) => Term::App(*f, args.iter().map(|a| shift(a, p)).collect()),
    }
}

/// All tuples of length `k` of numbers smaller than `n`, in lexicographic order.
fn tuples(n : usize, k : usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for_each_tuple(n, k, |t| result.push(t.to_vec()));
    result
}

/// Calls `f` on every tuple of length `k` of numbers smaller than `n`, in
/// lexicographic order.
fn for_each_tuple(n : usize, k : usize, mut f : impl FnMut(&[usize])) {
    if k > 0 && n == 0 {
        return;
    }
    let mut t = vec![0; k];
    loop {
        f(&t);
        let mut i = k;
        loop {
            if i == 0 {
                return;
            }
            i -= 1;
            t[i] += 1;
            if t[i] < n {
                break;
            }
            t[i] = 0;
        }
    }
}

/// The finite models of the theory of `T`, generated by k atoms that satisfy
/// `formula`, up to isomorphism, given by the tuples of these atoms. At most
/// `limit` models are returned.
fn generated_models<T : SymbolicTheory>(k : usize, formula : &Formula, limit : usize) -> Vec<Vec<SymbolicAtom<T>>> {
    let theory = T::theory();
    let signature = &theory.signature;
    assert!(signature.functions.iter().all(|(_, arity)| *arity > 0), "a symbolic theory cannot have constants");
    let order = order::<T>();
    let mut found = Vec::new();
    if k == 0 {
        // Without constants, no atoms generate the empty structure, which
        // satisfies every axiom. The formula has no variables, so no atoms.
        if matches!(nnf(formula, true, &mut |_| unreachable!()), Prop::Const(true)) && limit > 0 {
            found.push(Vec::new());
        }
        return found;
    }
    for size in 1..=T::generated_size_bound(k) {
        if found.len() >= limit {
            break;
        }
        let mut search = Search::new(signature, order, size);
        for axiom in &theory.axioms {
            search.axiom(axiom);
        }
        let values = search.description(k, formula);
        while found.len() < limit {
            match search.next_model(&values) {
                Some((structure, tuple)) => {
                    let structure = Rc::new(structure);
                    found.push(tuple.iter().map(|&e| SymbolicAtom::new(&structure, e)).collect());
                }
                None => break,
            }
        }
    }
    found
}

/// A propositional formula in negation normal form over the literals of the
/// solver.
enum Prop {
    Const(bool),
    Lit(Lit),
    And(Vec<Prop>),
    Or(Vec<Prop>),
}

impl Prop {
    fn negate_atom(self, positive : bool) -> Prop {
        match (self, positive) {
            (p, true) => p,
            (Prop::Const(b), false) => Prop::Const(!b),
            (Prop::Lit(l), false) => Prop::Lit(!l),
            _ => unreachable!("only atoms are negated"),
        }
    }

    /// The conjunction (if `and`) or the disjunction of `parts`, simplified.
    fn join(parts : Vec<Prop>, and : bool) -> Prop {
        let mut kept = Vec::new();
        for p in parts {
            match p {
                Prop::Const(b) if b == and => {}
                Prop::Const(b) => return Prop::Const(b),
                Prop::And(v) if and => kept.extend(v),
                Prop::Or(v) if !and => kept.extend(v),
                p => kept.push(p),
            }
        }
        match kept.len() {
            0 => Prop::Const(and),
            1 => kept.pop().unwrap(),
            _ if and => Prop::And(kept),
            _ => Prop::Or(kept),
        }
    }
}

/// The negation normal form of a formula, negated if `positive` is false, with
/// the atoms replaced by the values that `atom` gives them.
fn nnf(formula : &Formula, positive : bool, atom : &mut dyn FnMut(&Formula) -> Prop) -> Prop {
    match formula {
        Formula::True => Prop::Const(positive),
        Formula::False => Prop::Const(!positive),
        Formula::Eq(..) | Formula::Rel(..) => atom(formula).negate_atom(positive),
        Formula::Not(a) => nnf(a, !positive, atom),
        Formula::And(v) => Prop::join(v.iter().map(|a| nnf(a, positive, atom)).collect(), positive),
        Formula::Or(v) => Prop::join(v.iter().map(|a| nnf(a, positive, atom)).collect(), !positive),
    }
}

/// The atoms of a formula, without repetitions.
fn atoms_of(formula : &Formula, out : &mut Vec<Formula>) {
    match formula {
        Formula::True | Formula::False => {}
        Formula::Eq(..) | Formula::Rel(..) => {
            if !out.contains(formula) {
                out.push(formula.clone());
            }
        }
        Formula::Not(a) => atoms_of(a, out),
        Formula::And(v) | Formula::Or(v) => v.iter().for_each(|a| atoms_of(a, out)),
    }
}

/// The search for the models of a fixed size: a SAT problem whose variables
/// give the tables of the relations and of the functions. An element is given
/// by `size` literals, exactly one of which is true.
struct Search<'a> {
    solver : Solver<'static>,
    size : usize,
    order : usize,
    signature : &'a Signature,
    relations : Vec<Vec<Lit>>,
    functions : Vec<Vec<Vec<Lit>>>,
    truth : Lit,
}

impl<'a> Search<'a> {
    fn new(signature : &'a Signature, order : usize, size : usize) -> Self {
        let mut solver = Solver::new();
        let truth = solver.new_lit();
        solver.add_clause(&[truth]);
        let relations = signature
            .relations
            .iter()
            .enumerate()
            .map(|(r, (_, arity))| {
                if r == order { Vec::new() } else { (0..size.pow(*arity as u32)).map(|_| solver.new_lit()).collect() }
            })
            .collect();
        let mut search = Search { solver, size, order, signature, relations, functions : Vec::new(), truth };
        for (_, arity) in &signature.functions {
            let table = (0..size.pow(*arity as u32)).map(|_| search.element()).collect();
            search.functions.push(table);
        }
        search
    }

    fn position(&self, args : &[usize]) -> usize {
        args.iter().fold(0, |p, &a| p * self.size + a)
    }

    /// The literals of a new element.
    fn element(&mut self) -> Vec<Lit> {
        let lits : Vec<Lit> = (0..self.size).map(|_| self.solver.new_lit()).collect();
        self.solver.add_clause(&lits);
        for i in 0..lits.len() {
            for j in 0..i {
                self.solver.add_clause(&[!lits[i], !lits[j]]);
            }
        }
        lits
    }

    /// The value of an atom whose terms are variables, at an assignment of
    /// elements to the variables.
    fn atom_value(&self, atom : &Formula, assignment : &[usize]) -> Prop {
        let var = |t : &Term| match t {
            Term::Var(v) => assignment[*v],
            Term::App(..) => unreachable!("the formula is flat"),
        };
        match atom {
            Formula::Eq(s, t) => Prop::Const(var(s) == var(t)),
            Formula::Rel(r, args) => {
                let args : Vec<usize> = args.iter().map(var).collect();
                if *r == self.order {
                    Prop::Const(args[0] < args[1])
                } else {
                    Prop::Lit(self.relations[*r][self.position(&args)])
                }
            }
            _ => unreachable!("not an atom"),
        }
    }

    /// A literal that implies `p`.
    fn define(&mut self, p : &Prop) -> Lit {
        match p {
            Prop::Const(true) => self.truth,
            Prop::Const(false) => !self.truth,
            Prop::Lit(l) => *l,
            Prop::And(v) => {
                let a = self.solver.new_lit();
                for q in v {
                    let l = self.define(q);
                    self.solver.add_clause(&[!a, l]);
                }
                a
            }
            Prop::Or(v) => {
                let a = self.solver.new_lit();
                let mut clause = vec![!a];
                for q in v {
                    clause.push(self.define(q));
                }
                self.solver.add_clause(&clause);
                a
            }
        }
    }

    /// Adds the condition that `p` holds.
    fn require(&mut self, p : &Prop) {
        match p {
            Prop::Const(true) => {}
            Prop::Const(false) => self.solver.add_clause(&[!self.truth]),
            Prop::Lit(l) => self.solver.add_clause(&[*l]),
            Prop::And(v) => v.iter().for_each(|q| self.require(q)),
            Prop::Or(v) => {
                let clause : Vec<Lit> = v.iter().map(|q| self.define(q)).collect();
                self.solver.add_clause(&clause);
            }
        }
    }

    /// Adds the instances of an axiom. The terms are flattened: each
    /// application f(u) is replaced by a new variable v, and the instance is
    /// required when f(u) = v.
    fn axiom(&mut self, axiom : &Axiom) {
        let (flat, definitions) = flatten(&axiom.formula, axiom.variables.len());
        let count = axiom.variables.len() + definitions.len();
        let mut instances = Vec::new();
        for_each_tuple(self.size, count, |assignment| {
            let mut parts : Vec<Prop> = definitions
                .iter()
                .map(|(f, args, v)| {
                    let args : Vec<usize> = args.iter().map(|&i| assignment[i]).collect();
                    Prop::Lit(!self.functions[*f][self.position(&args)][assignment[*v]])
                })
                .collect();
            parts.push(nnf(&flat, true, &mut |atom| self.atom_value(atom, assignment)));
            instances.push(Prop::join(parts, false));
        });
        for p in &instances {
            self.require(p);
        }
    }

    /// Adds the conditions that `k` atoms satisfy `formula` and generate the
    /// structure, and returns the literals of these atoms.
    fn description(&mut self, k : usize, formula : &Formula) -> Vec<Vec<Lit>> {
        let (flat, definitions) = flatten(formula, k);
        let mut values : Vec<Vec<Lit>> = (0..k + definitions.len()).map(|_| self.element()).collect();
        // The value of v is f(u) when the definition (f, u, v) holds.
        let mut clauses = Vec::new();
        for (f, args, v) in &definitions {
            for_each_tuple(self.size, args.len() + 1, |t| {
                let (e, t) = t.split_last().unwrap();
                let mut clause : Vec<Lit> = args.iter().zip(t).map(|(&u, &a)| !values[u][a]).collect();
                clause.push(!self.functions[*f][self.position(t)][*e]);
                clause.push(values[*v][*e]);
                clauses.push(clause);
            });
        }
        for clause in &clauses {
            self.solver.add_clause(clause);
        }
        // A literal for each atom of the formula, equivalent to it.
        let mut atoms = Vec::new();
        atoms_of(&flat, &mut atoms);
        let mut literals : BTreeMap<Formula, Lit> = BTreeMap::new();
        for atom in atoms {
            let l = self.atom_literal(&atom, &values);
            literals.insert(atom, l);
        }
        let p = nnf(&flat, true, &mut |atom| Prop::Lit(literals[atom]));
        self.require(&p);
        values.truncate(k);
        self.generated(&values);
        values
    }

    /// A literal equivalent to an atom whose terms are variables with the
    /// given values.
    fn atom_literal(&mut self, atom : &Formula, values : &[Vec<Lit>]) -> Lit {
        let mut vars : Vec<usize> = Vec::new();
        atom.for_each_term(&mut |t| {
            if let Term::Var(v) = t
                && !vars.contains(v)
            {
                vars.push(*v);
            }
        });
        let lit = self.solver.new_lit();
        let mut clauses = Vec::new();
        let mut assignment = vec![0; values.len()];
        for_each_tuple(self.size, vars.len(), |t| {
            for (&v, &e) in vars.iter().zip(t) {
                assignment[v] = e;
            }
            let condition : Vec<Lit> = vars.iter().zip(t).map(|(&v, &e)| !values[v][e]).collect();
            match self.atom_value(atom, &assignment) {
                Prop::Const(b) => clauses.push([&condition[..], &[if b { lit } else { !lit }]].concat()),
                Prop::Lit(r) => {
                    clauses.push([&condition[..], &[!lit, r]].concat());
                    clauses.push([&condition[..], &[lit, !r]].concat());
                }
                _ => unreachable!(),
            }
        });
        for clause in &clauses {
            self.solver.add_clause(clause);
        }
        lit
    }

    /// Adds the condition that every element is the value of a term in the
    /// `generators`. reached[e] implies that e is the value of a term of depth
    /// at most the current level; size - 1 levels suffice.
    fn generated(&mut self, generators : &[Vec<Lit>]) {
        let mut reached : Vec<Lit> = Vec::new();
        for e in 0..self.size {
            let l = self.solver.new_lit();
            let mut clause = vec![!l];
            clause.extend(generators.iter().map(|x| x[e]));
            self.solver.add_clause(&clause);
            reached.push(l);
        }
        if !self.signature.functions.is_empty() {
            for _ in 1..self.size {
                let mut next = Vec::new();
                for e in 0..self.size {
                    let l = self.solver.new_lit();
                    let mut clause = vec![!l, reached[e]];
                    for (f, (_, arity)) in self.signature.functions.iter().enumerate() {
                        for args in tuples(self.size, *arity) {
                            let a = self.solver.new_lit();
                            for &u in &args {
                                self.solver.add_clause(&[!a, reached[u]]);
                            }
                            let value = self.functions[f][self.position(&args)][e];
                            self.solver.add_clause(&[!a, value]);
                            clause.push(a);
                        }
                    }
                    self.solver.add_clause(&clause);
                    next.push(l);
                }
                reached = next;
            }
        }
        for l in reached {
            self.solver.add_clause(&[l]);
        }
    }

    /// The next model with the atoms `values`, as a structure and the tuple of
    /// the atoms, if there is one. The model is then excluded from the search.
    fn next_model(&mut self, values : &[Vec<Lit>]) -> Option<(FiniteStructure, Vec<usize>)> {
        if !self.solver.solve().expect("the SAT solver failed") {
            return None;
        }
        let model : BTreeSet<Lit> = self.solver.model().unwrap().into_iter().collect();
        let value = |l : Lit| model.contains(&l);
        let element = |lits : &Vec<Lit>| lits.iter().position(|&l| value(l)).unwrap();
        let relations : Vec<Vec<bool>> = self.relations.iter().map(|t| t.iter().map(|&l| value(l)).collect()).collect();
        let functions : Vec<Vec<usize>> = self.functions.iter().map(|t| t.iter().map(element).collect()).collect();
        let tuple : Vec<usize> = values.iter().map(element).collect();
        let mut block = Vec::new();
        for (lits, table) in self.relations.iter().zip(&relations) {
            block.extend(lits.iter().zip(table).map(|(&l, &b)| if b { !l } else { l }));
        }
        for (lits, table) in self.functions.iter().zip(&functions) {
            block.extend(lits.iter().zip(table).map(|(element, &e)| !element[e]));
        }
        block.extend(values.iter().zip(&tuple).map(|(element, &e)| !element[e]));
        self.solver.add_clause(&block);
        Some((FiniteStructure { id : fresh_id(), size : self.size, relations, functions }, tuple))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::parse_description;

    type Tuple<T> = SymbolicOrbit<T, Vec<SymbolicAtom<T>>>;

    fn orbit<T : SymbolicTheory>(src : &str, atoms : &[&str]) -> std::result::Result<Tuple<T>, DescriptionError> {
        let atoms : Vec<String> = atoms.iter().map(|a| a.to_string()).collect();
        orbit_of::<T>(&parse_description(src, &T::theory().signature, &atoms).unwrap())
    }

    /// The formula x1 < x2 < ... < xn, shifted by `p`.
    fn increasing(n : usize, p : usize) -> Formula {
        Formula::And((1..n).map(|i| Formula::Rel(0, vec![Term::Var(p + i - 1), Term::Var(p + i)])).collect())
    }

    /// A set of n atoms of the orbit given by the formula of `increasing`.
    fn increasing_set<T : SymbolicTheory>(n : usize) -> BTreeSet<SymbolicAtom<T>> {
        let description = Description { variables : (1..=n).map(|i| format!("x{i}")).collect(), formula : increasing(n, 0) };
        orbit_of::<T>(&description).unwrap().evaluate(|t| t.iter().cloned().collect())
    }

    fn binomial(n : usize, k : usize) -> usize {
        if k > n { 0 } else { (0..k).fold(1, |b, i| b * (n - i) / (i + 1)) }
    }

    #[test]
    fn orbits_of_descriptions() {
        let xy = ["x", "y"];
        assert!(orbit::<DenseOrder>("x < y", &xy).is_ok());
        assert!(orbit::<DenseOrder>("x = y", &xy).is_ok());
        assert!(orbit::<DenseOrder>("y > x", &xy).unwrap() == orbit::<DenseOrder>("x < y", &xy).unwrap());
        assert!(orbit::<DenseOrder>("y < x", &xy).unwrap() != orbit::<DenseOrder>("x < y", &xy).unwrap());
        assert_eq!(orbit::<DenseOrder>("x < y & y < x", &xy).err(), Some(DescriptionError::InconsistentFormula));
        assert!(matches!(orbit::<DenseOrder>("x != y", &xy), Err(DescriptionError::AmbiguousFormula(..))));
        assert!(matches!(orbit::<DenseOrder>("true", &xy), Err(DescriptionError::AmbiguousFormula(..))));
        // In a tree, two incomparable points and their meet.
        let xym = ["x", "y", "m"];
        let xyz = ["x", "y", "z"];
        assert!(orbit::<MeetTree>("x < y & !le(x, y) & m = meet(x, y)", &xym).is_ok());
        assert!(matches!(orbit::<MeetTree>("x < y & m = meet(x, y)", &xym), Err(DescriptionError::AmbiguousFormula(..))));
        assert_eq!(orbit::<MeetTree>("le(y, x) & x < y", &xy).err(), Some(DescriptionError::InconsistentFormula));
        // The meet is below x, so it comes before x.
        assert_eq!(orbit::<MeetTree>("x < y & y < z & meet(x, z) = y", &xyz).err(), Some(DescriptionError::InconsistentFormula));
    }

    #[test]
    fn describe_gives_back_the_orbit() {
        let xyz = ["x", "y", "z"];
        for src in ["x < y & y < z", "x = z & y < x", "z < x & x = y"] {
            let o = orbit::<DenseOrder>(src, &xyz).unwrap();
            assert!(orbit_of::<DenseOrder>(&describe(&o)).unwrap() == o, "{src}");
        }
        for src in ["x < y & y < z & meet(y, z) = x", "x < y & y < z & meet(x, y) = meet(y, z) & meet(x, y) != x"] {
            let o = orbit::<MeetTree>(src, &xyz).unwrap();
            assert!(orbit_of::<MeetTree>(&describe(&o)).unwrap() == o, "{src}");
        }
    }

    /// In (Q, <), the orbits of pairs of sets of sizes n and m: S ∪ T has k
    /// elements, S is any n of them, and T contains the k - n others and
    /// n + m - k elements of S.
    #[test]
    fn product_orbits_of_the_dense_order() {
        for n in 0..=3 {
            for m in 0..=3 {
                let reps = SymbolicAtom::<DenseOrder>::orbits_in_product(&increasing_set(n), &increasing_set(m));
                let expected : usize = (n.max(m)..=n + m).map(|k| binomial(k, n) * binomial(n, n + m - k)).sum();
                assert_eq!(reps.len(), expected, "n = {n}, m = {m}");
                for i in 0..reps.len() {
                    for j in 0..i {
                        assert!(reps[i] != reps[j]);
                    }
                }
            }
        }
    }

    /// In the tree, the orbits of k-element sets are counted by c_k, and those
    /// of pairs of sets by the formula of the test of `Tree::orbits_in_product`.
    #[test]
    fn product_orbits_of_the_tree() {
        let c : [usize; 5] = [1, 1, 2, 8, 40];
        for (k, &ck) in c.iter().enumerate() {
            assert_eq!(generated_models::<MeetTree>(k, &increasing(k, 0), usize::MAX).len(), ck, "k = {k}");
        }
        let factorial = |k : usize| -> usize { (1..=k).product() };
        for (n, m) in [(1, 1), (1, 2), (2, 1), (2, 2), (1, 3)] {
            let expected : usize = (n.max(m)..=n + m)
                .map(|k| c[k] * factorial(k) / (factorial(k - m) * factorial(k - n) * factorial(n + m - k)))
                .sum();
            let formula = Formula::And(vec![increasing(n, 0), increasing(m, n)]);
            assert_eq!(generated_models::<MeetTree>(n + m, &formula, usize::MAX).len(), expected, "n = {n}, m = {m}");
        }
        // Two points: equal, below, above, and incomparable in two orders.
        assert_eq!(SymbolicAtom::<MeetTree>::orbits_in_product(&increasing_set(1), &increasing_set(1)).len(), 5);
    }

    /// The Gröbner basis algorithms on symbolic atoms, on the examples of the
    /// tests of `equivariant.rs` for the atoms `DLO` and `Tree`.
    mod groebner {
        use super::*;
        use crate::equivariant::{
            equivariant_buchberger, equivariant_groebner_basis, minimal_basis, one_colour_groebner_basis,
            reduces_to_zero, PolynomialOrbit,
        };
        use crate::mon::Polynomial;
        use num_rational::Rational64 as Q;
        use num_traits::Pow;

        type P<T> = Polynomial<Q, SymbolicAtom<T>>;

        /// The orbit of f(x1, ..., xk), where the tuple (x1, ..., xk) is in the
        /// orbit given by the description.
        fn polynomial<T : SymbolicTheory>(description : &str, k : usize, f : impl Fn(&[P<T>]) -> P<T>)
            -> PolynomialOrbit<Q, SymbolicAtom<T>> {
            let names : Vec<String> = (1..=k).map(|i| format!("x{i}")).collect();
            let names : Vec<&str> = names.iter().map(|n| n.as_str()).collect();
            orbit::<T>(description, &names)
                .unwrap()
                .map(|t| f(&t.iter().map(|a| Polynomial::var(a.clone())).collect::<Vec<_>>()))
        }

        #[test]
        fn products_in_the_dense_order() {
            let g = polynomial::<DenseOrder>("x1 < x2 & x2 < x3", 3, |x| x[0].clone() * x[1].clone() - x[2].clone());
            // The weak basis has the same minimal basis as with `DLO`, up to the
            // order: the monic generator, x1 x2^2 - x1 x2 and x1^2 x2 - x1 x2.
            // It misses x2 - x1.
            let weak = equivariant_buchberger(vec![g.clone()], 50).ok().unwrap();
            let cubic = |e1 : u8, e2 : u8| {
                polynomial::<DenseOrder>("x1 < x2", 2, move |x| {
                    x[0].clone().pow(e1) * x[1].clone().pow(e2) - x[0].clone() * x[1].clone()
                })
            };
            let monic = polynomial::<DenseOrder>("x1 < x2 & x2 < x3", 3, |x| x[2].clone() - x[0].clone() * x[1].clone());
            let minimal = minimal_basis(weak.clone());
            assert_eq!(minimal.len(), 3);
            assert!([monic, cubic(1, 2), cubic(2, 1)].iter().all(|o| minimal.contains(o)));
            let basis = equivariant_groebner_basis(vec![g.clone()], 50).ok().unwrap();
            let difference = polynomial::<DenseOrder>("x1 < x2", 2, |x| x[1].clone() - x[0].clone());
            let idempotent = polynomial::<DenseOrder>("true", 1, |x| x[0].clone() * x[0].clone() - x[0].clone());
            assert!(!difference.evaluate(|f| reduces_to_zero(f, &weak)));
            assert!(minimal_basis(basis) == vec![difference.clone(), idempotent]);
            let basis = one_colour_groebner_basis(vec![g], 50).ok().unwrap();
            assert!(difference.evaluate(|f| reduces_to_zero(f, &basis)));
        }

        #[test]
        fn differences_along_the_tree_order() {
            let g = polynomial::<MeetTree>("le(x1, x2) & x1 != x2", 2, |x| x[1].clone() - x[0].clone());
            let incomparable = polynomial::<MeetTree>("x1 < x2 & !le(x1, x2)", 2, |x| x[1].clone() - x[0].clone());
            let weak = equivariant_buchberger(vec![g.clone()], 50).ok().unwrap();
            assert!(weak == vec![g.clone()]);
            assert!(!incomparable.evaluate(|f| reduces_to_zero(f, &weak)));
            let minimal = minimal_basis(equivariant_groebner_basis(vec![g.clone()], 50).ok().unwrap());
            assert_eq!(minimal.len(), 2);
            assert!(minimal.contains(&g) && minimal.contains(&incomparable));
            let basis = one_colour_groebner_basis(vec![g], 50).ok().unwrap();
            assert!(incomparable.evaluate(|f| reduces_to_zero(f, &basis)));
        }
    }
}
