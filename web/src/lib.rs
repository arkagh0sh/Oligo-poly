//! The interface of the web page: one function from a JSON request to a JSON
//! answer, exported to JavaScript as plain WebAssembly functions.
//!
//! The page calls the exports in this order: `alloc(n)` gives a buffer for
//! the n bytes of the request; `compute(ptr, n)` reads and frees it, runs the
//! request, and returns the length of the answer; `output_ptr()` gives the
//! address of the answer. If the computation panics, the panic hook writes an
//! answer with the status `internal-error` before the module traps, so the
//! page can still read it with `output_len()` and `output_ptr()`.

use std::cell::RefCell;
use std::sync::Once;
use num_rational::BigRational;
use serde::{Deserialize, Serialize};
use atomic_hilbert::equivariant::{
    equivariant_groebner_basis, minimal_basis, one_colour_groebner_basis, reduce_tails, PolynomialOrbit,
};
use atomic_hilbert::generator::{parse_generator, show_generator};
use atomic_hilbert::symbolic::{DenseOrder, MeetTree, SymbolicAtom, SymbolicTheory};

/// The structure of the atoms.
#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Theory {
    /// The dense linear order (Q, <).
    Dense,
    /// The dense meet-tree with a lexicographic order.
    Tree,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Algorithm {
    /// The colouring of Section 5 of Ghosh and Lopez.
    Colouring,
    /// The variant with at most one high variable.
    OneColour,
}

#[derive(Clone, Debug, Deserialize)]
pub struct Request {
    pub theory : Theory,
    pub algorithm : Algorithm,
    /// The generators, one per line; `#` starts a comment.
    pub generators : String,
    /// The limit on the number of (coloured) orbits of the computation.
    pub max_orbits : usize,
}

/// A line that is not a generator.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LineError {
    /// The number of the line, from 1.
    pub line : usize,
    pub message : String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum Response {
    /// The minimal basis with reduced tails, and the number of orbits of the
    /// basis before it was made minimal.
    Basis { basis : Vec<String>, orbits : usize },
    /// Some lines are not generators.
    InvalidGenerators { errors : Vec<LineError> },
    /// There are no generators.
    NoGenerators,
    /// The computation needs more orbits than allowed; the orbits found so far.
    Limit { partial : Vec<String> },
    /// The request is malformed.
    BadRequest { message : String },
    /// The computation panicked.
    InternalError { message : String },
}

/// Answers a request written in JSON.
pub fn run(request : &str) -> Response {
    match serde_json::from_str::<Request>(request) {
        Ok(request) => match request.theory {
            Theory::Dense => basis_of::<DenseOrder>(&request),
            Theory::Tree => basis_of::<MeetTree>(&request),
        },
        Err(e) => Response::BadRequest { message : e.to_string() },
    }
}

type Orbits<T> = Vec<PolynomialOrbit<BigRational, SymbolicAtom<T>>>;

fn show_all<T : SymbolicTheory>(orbits : &Orbits<T>) -> Vec<String> {
    orbits.iter().map(show_generator).collect()
}

fn basis_of<T : SymbolicTheory>(request : &Request) -> Response {
    let mut generators : Orbits<T> = Vec::new();
    let mut errors = Vec::new();
    for (i, line) in request.generators.lines().enumerate() {
        // The text before `#`, untrimmed, so that the positions of the errors
        // count from the start of the line.
        let text = line.split('#').next().unwrap_or("");
        if text.trim().is_empty() {
            continue;
        }
        match parse_generator::<T, BigRational>(text) {
            Ok(g) => generators.push(g),
            Err(e) => errors.push(LineError { line : i + 1, message : e.to_string() }),
        }
    }
    if !errors.is_empty() {
        return Response::InvalidGenerators { errors };
    }
    if generators.is_empty() {
        return Response::NoGenerators;
    }
    let result = match request.algorithm {
        Algorithm::Colouring => equivariant_groebner_basis(generators, request.max_orbits),
        Algorithm::OneColour => one_colour_groebner_basis(generators, request.max_orbits),
    };
    match result {
        Ok(basis) => {
            let orbits = basis.len();
            Response::Basis { basis : show_all(&reduce_tails(minimal_basis(basis))), orbits }
        }
        Err(partial) => Response::Limit { partial : show_all(&partial) },
    }
}

thread_local! {
    static OUTPUT : RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

fn set_output(response : &Response) -> usize {
    let bytes = serde_json::to_vec(response).unwrap_or_default();
    let len = bytes.len();
    OUTPUT.with(|o| {
        if let Ok(mut o) = o.try_borrow_mut() {
            *o = bytes;
        }
    });
    len
}

static HOOK : Once = Once::new();

/// Writes the message of a panic as the answer.
fn install_panic_hook() {
    HOOK.call_once(|| {
        std::panic::set_hook(Box::new(|info| {
            set_output(&Response::InternalError { message : info.to_string() });
        }))
    });
}

/// A buffer of `len` bytes, for the request.
#[unsafe(no_mangle)]
pub extern "C" fn alloc(len : usize) -> *mut u8 {
    let mut buffer = Vec::<u8>::with_capacity(len);
    let ptr = buffer.as_mut_ptr();
    std::mem::forget(buffer);
    ptr
}

/// Answers the request of `len` bytes at `ptr`, which must come from `alloc`,
/// and returns the length of the answer.
///
/// # Safety
///
/// `ptr` must have been returned by `alloc(len)`, and the `len` bytes must have
/// been written. The buffer is freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn compute(ptr : *mut u8, len : usize) -> usize {
    install_panic_hook();
    OUTPUT.with(|o| o.borrow_mut().clear());
    let bytes = unsafe { Vec::from_raw_parts(ptr, len, len) };
    let response = match String::from_utf8(bytes) {
        Ok(request) => run(&request),
        Err(_) => Response::BadRequest { message : "the request is not UTF-8".to_string() },
    };
    set_output(&response)
}

/// The address of the answer.
#[unsafe(no_mangle)]
pub extern "C" fn output_ptr() -> *const u8 {
    OUTPUT.with(|o| o.borrow().as_ptr())
}

/// The length of the answer, also after a panic.
#[unsafe(no_mangle)]
pub extern "C" fn output_len() -> usize {
    OUTPUT.with(|o| o.borrow().len())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(theory : &str, algorithm : &str, generators : &str) -> String {
        serde_json::json!({ "theory" : theory, "algorithm" : algorithm, "generators" : generators, "max_orbits" : 200 }).to_string()
    }

    fn basis(theory : &str, algorithm : &str, generators : &str) -> Vec<String> {
        match run(&request(theory, algorithm, generators)) {
            Response::Basis { mut basis, .. } => {
                basis.sort();
                basis
            }
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn examples_of_the_page() {
        for algorithm in ["colouring", "one-colour"] {
            assert_eq!(basis("dense", algorithm, "x < y & y < z : x*y - z"), ["true : x1^2 - x1", "x1 < x2 : x2 - x1"]);
            assert_eq!(basis("dense", algorithm, "x < y : x^2 - y"), ["true : x1^2 - x1", "x1 < x2 : x2 - x1"]);
            assert_eq!(
                basis("dense", algorithm, "x < y : y - x  # the diagonal\nx^2 - 1"),
                ["true : x1^2 - 1", "x1 < x2 : x2 - x1"]
            );
            assert_eq!(
                basis("tree", algorithm, "le(x, y) & x != y : y - x"),
                ["x1 < x2 & le(x1, x2) : x2 - x1", "x1 < x2 & meet(x1, x2) < x1 : x2 - x1"]
            );
        }
    }

    #[test]
    fn errors_are_reported_by_line() {
        let response = run(&request("dense", "colouring", "x < y : x*y - z\n\n  # a comment\nx < y & y < x : x\nx < y : x +"));
        let Response::InvalidGenerators { errors } = response else { panic!("{response:?}") };
        assert_eq!(errors.iter().map(|e| e.line).collect::<Vec<_>>(), [1, 4, 5]);
        assert!(errors[0].message.starts_with("the description allows several orbits"));
        assert_eq!(errors[1].message, "no atoms satisfy the description");
        assert_eq!(errors[2].message, "in the polynomial: at character 12: unexpected end of the polynomial");
        assert_eq!(run(&request("dense", "colouring", "# nothing\n")), Response::NoGenerators);
        assert!(matches!(run("{}"), Response::BadRequest { .. }));
    }

    #[test]
    fn the_limit_on_orbits() {
        let request = serde_json::json!({
            "theory" : "dense", "algorithm" : "colouring", "generators" : "x < y & y < z : x*y - z", "max_orbits" : 2
        });
        assert!(matches!(run(&request.to_string()), Response::Limit { .. }));
    }

    #[test]
    fn the_answer_is_json() {
        let answer = serde_json::to_string(&run(&request("dense", "colouring", "x^2 - x"))).unwrap();
        assert_eq!(answer, r#"{"status":"basis","basis":["true : x1^2 - x1"],"orbits":1}"#);
    }
}
