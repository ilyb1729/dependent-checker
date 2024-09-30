// mod ast;
mod lambdapi;

// use crate::ast::{eval_inf, quote0, Name, TermCheck, TermInfer, Type};

fn main() {
    // let id = TermCheck::Lam(Box::new(TermCheck::Inf(Box::new(TermInfer::Bound(0)))));
    // let tfree = |s: &str| Type::TFree(Name::Global(s.to_string()));
    // let free = |s: &str| TermCheck::Inf(Box::new(TermInfer::Free(Name::Global(s.to_string()))));
    // let term1 = TermInfer::App(
    //     Box::new(TermInfer::Ann(
    //         Box::new(id),
    //         Box::new(Type::Fun(Box::new(tfree("a")), Box::new(tfree("a")))),
    //     )),
    //     Box::new(free("y")),
    // );
    // println!("{:?}", quote0(eval_inf(term1, VecDeque::new())));
}
