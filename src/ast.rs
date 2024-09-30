use std::collections::VecDeque;

trait Callable {
    fn call(&self, arg: Value) -> Value;
}

impl<F> Callable for F
where
    F: Fn(Value) -> Value + 'static,
{
    fn call(&self, arg: Value) -> Value {
        self(arg)
    }
}

#[derive(Clone, Debug)]
pub enum TermInfer {
    Ann(Box<TermCheck>, Box<Type>),
    Bound(usize), // DeBrujin Index
    Free(Name),
    App(Box<TermInfer>, Box<TermCheck>),
}
#[derive(Clone, Debug)]
pub enum TermCheck {
    Inf(Box<TermInfer>),
    Lam(Box<TermCheck>),
}
#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    TFree(Name),
    Fun(Box<Type>, Box<Type>),
}
pub enum Value {
    VLam(Box<dyn Callable>), // This is going to take some thought how to represent functions
    VNeutral(Box<Neutral>),
}
impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Value::VLam(_) => panic!("Cannot clone VLam"),
            Value::VNeutral(n) => Value::VNeutral(n.clone()),
        }
    }
}
#[derive(Clone, PartialEq, Debug)]
pub enum Name {
    Global(String),
    Local(usize),
    Quote(usize),
}
#[derive(Clone)]
enum Neutral {
    NFree(Name),
    NApp(Box<Neutral>, Box<Value>),
}

fn vfree(n: Name) -> Value {
    Value::VNeutral(Box::new(Neutral::NFree(n)))
}

pub type Env = VecDeque<Value>;

pub fn eval_inf(t_i: TermInfer, env: Env) -> Value {
    match t_i {
        TermInfer::Ann(e, _) => eval_check(*e, env),
        TermInfer::Free(x) => vfree(x),
        TermInfer::Bound(i) => env[i].clone(),
        TermInfer::App(e, ep) => vapp(&eval_inf(*e, env.clone()), &eval_check(*ep, env.clone())),
    }
}

fn vapp(v1: &Value, v2: &Value) -> Value {
    match v1 {
        Value::VLam(f) => f.call(v2.clone()), // apply lambda to value
        Value::VNeutral(n) => {
            Value::VNeutral(Box::new(Neutral::NApp(n.clone(), Box::new(v2.clone()))))
        }
    }
}

fn eval_check(t_c: TermCheck, env: Env) -> Value {
    match t_c {
        TermCheck::Inf(e) => eval_inf(*e, env),
        TermCheck::Lam(e) => {
            let closure = move |x: Value| -> Value {
                let mut new_env = env.clone();
                new_env.push_front(x.clone());
                eval_check((*e).clone(), new_env)
            };
            Value::VLam(Box::new(closure))
        }
    }
}

// Type stuff

#[derive(Clone)]
enum Kind {
    Star,
}

#[derive(Clone)]
enum Info {
    HasKind(Kind),
    HasType(Type),
}

type Context = VecDeque<(Name, Info)>;

// make sure that the kind exists when referenced
fn kind_check(c: Context, t: Type, k: Kind) -> Result<(), &'static str> {
    match t {
        Type::TFree(n) => {
            c.iter()
                .position(|r| {
                    if let Info::HasKind(_) = r.1 {
                        r.0 == n
                    } else {
                        false
                    }
                })
                .ok_or("unknown identifier")?;
            Ok(())
        }
        Type::Fun(d, r) => {
            kind_check(c.clone(), *d, Kind::Star)?;
            kind_check(c.clone(), *r, Kind::Star)
        }
    }
}

fn type_inf0(c: Context, t_i: TermInfer) -> Result<Type, &'static str> {
    type_inf(0, c, t_i)
}
fn type_inf(i: usize, c: Context, t_i: TermInfer) -> Result<Type, &'static str> {
    match t_i {
        TermInfer::Ann(e, ty) => {
            kind_check(c.clone(), *ty.clone(), Kind::Star)?;
            type_check(i, c.clone(), *e, *ty.clone())?;
            Ok(*ty)
        }
        TermInfer::App(e1, e2) => {
            let sigma = type_inf(i, c.clone(), *e1)?;
            if let Type::Fun(ty1, ty2) = sigma {
                type_check(i, c.clone(), *e2, *ty1)?;
                Ok(*ty2)
            } else {
                Err("Illegal application")
            }
        }
        TermInfer::Free(x) => {
            let index = c
                .iter()
                .position(|r| {
                    if let Info::HasType(_) = r.1 {
                        r.0 == x
                    } else {
                        false
                    }
                })
                .ok_or("Unknown identifier")?;
            if let Info::HasType(ty) = &c[index].1 {
                // This is verbose for no reason...
                Ok(ty.clone())
            } else {
                Err("Unknown identifier")
            }
        }
        _ => Err("idk"),
    }
}

fn type_check(i: usize, c: Context, t_c: TermCheck, ty: Type) -> Result<(), &'static str> {
    match t_c {
        TermCheck::Inf(t_i) => {
            let ty2 = type_inf(i, c, *t_i)?;
            if ty2 != ty {
                Err("Type mismatch")
            } else {
                Ok(())
            }
        }
        TermCheck::Lam(t_c) => {
            if let Type::Fun(ty1, ty2) = ty {
                let mut new_env = c.clone();
                new_env.push_front((Name::Local(i), Info::HasType(*ty1)));
                type_check(
                    i + 1,
                    c,
                    subst_check(0, TermInfer::Free(Name::Local(i)), *t_c),
                    *ty2,
                )
            } else {
                Err("Type mismatch")
            }
        }
    }
}

fn subst_check(i: usize, t1: TermInfer, t2: TermCheck) -> TermCheck {
    match t2 {
        TermCheck::Inf(t_i) => TermCheck::Inf(Box::new(subst_inf(i, t1, *t_i))),
        TermCheck::Lam(t_c) => TermCheck::Lam(Box::new(subst_check(i + 1, t1, *t_c))),
    }
}
fn subst_inf(i: usize, t1: TermInfer, t2: TermInfer) -> TermInfer {
    match t2 {
        TermInfer::Ann(t_c, ty) => TermInfer::Ann(Box::new(subst_check(i, t1, *t_c)), ty),
        TermInfer::Free(y) => TermInfer::Free(y),
        TermInfer::Bound(j) => {
            if i == j {
                t1
            } else {
                TermInfer::Bound(j)
            }
        }
        TermInfer::App(t3, t4) => TermInfer::App(
            Box::new(subst_inf(i, t1.clone(), *t3)),
            Box::new(subst_check(i, t1.clone(), *t4)),
        ),
    }
}

pub fn quote0(v: Value) -> TermCheck {
    quote(0, v)
}
fn quote(i: usize, v: Value) -> TermCheck {
    match v {
        Value::VLam(f) => TermCheck::Lam(Box::new(quote(i + 1, f.call(vfree(Name::Quote(i)))))),
        Value::VNeutral(n) => TermCheck::Inf(Box::new(neutral_quote(i, *n))),
    }
}

fn neutral_quote(i: usize, n: Neutral) -> TermInfer {
    match n {
        Neutral::NFree(n) => bound_free(i, n),
        Neutral::NApp(n, v) => {
            TermInfer::App(Box::new(neutral_quote(i, *n)), Box::new(quote(i, *v)))
        }
    }
}

fn bound_free(i: usize, n: Name) -> TermInfer {
    match n {
        Name::Quote(j) => TermInfer::Bound(i - j - 1),
        _ => TermInfer::Free(n),
    }
}
