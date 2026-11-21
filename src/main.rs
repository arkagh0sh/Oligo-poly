use atomic_hilbert::bits::F2;
use atomic_hilbert::ideal::buchberger;
use atomic_hilbert::mon::Polynomial;

fn main() {
    let x : Polynomial<F2,String> = Polynomial::var("x".to_string());
    let y : Polynomial<F2,String> = Polynomial::var("y".to_string());
    let z : Polynomial<F2,String> = Polynomial::var("z".to_string());
    let f = x.clone() + y.clone()*z.clone();
    let g = x.clone()*y.clone();
    let vec_poly = vec![g,f];
    println!("{:?}",buchberger(vec_poly));
}
