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

#[derive(Clone, Debug, PartialEq)]
pub enum TermInfer {
    Ann(Box<TermCheck>, Box<TermCheck>),
    Star,
    Pi(Box<TermCheck>, Box<TermCheck>),
    Bound(usize), // DeBrujin Index
    Free(Name),
    App(Box<TermInfer>, Box<TermCheck>),
}
#[derive(Clone, Debug, PartialEq)]
pub enum TermCheck {
    Inf(Box<TermInfer>),
    Lam(Box<TermCheck>),
}
type Type = Value;

pub enum Value {
    VLam(Box<dyn Callable>), // This is going to take some thought how to represent functions
    VStar,
    VPi(Box<Value>, Box<dyn Callable>),
    VNeutral(Box<Neutral>),
}
impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Value::VLam(_) => panic!("Cannot clone VLam"),
            Value::VPi(_, _) => panic!("Cannot clone VPi"),
            Value::VStar => Value::VStar,
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
        TermInfer::Star => Value::VStar,
        TermInfer::Pi(ty1, ty2) => {
            let tmp_env = env.clone();
            let closure = move |x: Value| -> Value {
                let mut new_env = tmp_env.clone();
                new_env.push_front(x);
                eval_check(*ty2.clone(), new_env)
            };
            Value::VPi(Box::new(eval_check(*ty1, env.clone())), Box::new(closure))
        }
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
        Value::VStar => panic!("Unallowed application"),
        Value::VPi(_, _) => panic!("idk what to do"), // ??
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

type Context = VecDeque<(Name, Type)>;

fn type_inf0(c: Context, t_i: TermInfer) -> Result<Type, &'static str> {
    type_inf(0, c, t_i)
}
fn type_inf(i: usize, c: Context, t_i: TermInfer) -> Result<Type, &'static str> {
    match t_i {
        TermInfer::Star => Ok(Type::VStar),
        TermInfer::Pi(ty1, ty2) => {
            type_check(i, c.clone(), *ty1.clone(), Type::VStar)?;
            let tau = eval_check(*ty1, VecDeque::new());
            let mut new_env = c.clone();
            new_env.push_front((Name::Local(i), tau));
            type_check(
                i + 1,
                new_env,
                subst_check(0, TermInfer::Free(Name::Local(i)), *ty2),
                Type::VStar,
            )?;
            Ok(Type::VStar)
        }
        TermInfer::Ann(e, ty) => {
            type_check(i, c.clone(), *ty.clone(), Type::VStar)?;
            let tau = eval_check(*ty.clone(), VecDeque::new());
            type_check(i, c.clone(), *e, tau.clone())?;
            Ok(tau)
        }
        TermInfer::App(e1, e2) => {
            let sigma = type_inf(i, c.clone(), *e1)?;
            if let Type::VPi(ty1, ty2) = sigma {
                type_check(i, c.clone(), *e2.clone(), *ty1)?;
                Ok(ty2.call(eval_check(*e2.clone(), VecDeque::new())))
            } else {
                Err("Illegal application")
            }
        }
        TermInfer::Free(x) => {
            let index = c
                .iter()
                .position(|r| r.0 == x)
                .ok_or("Unknown identifier")?;
            Ok(c[index].1.clone())
        }

        _ => Err("idk"),
    }
}

fn type_check(i: usize, c: Context, t_c: TermCheck, ty: Type) -> Result<(), &'static str> {
    match t_c {
        TermCheck::Inf(t_i) => {
            let ty2 = type_inf(i, c, *t_i)?;
            // check equality of the types
            if quote0(ty2) != quote0(ty) {
                Err("Type mismatch")
            } else {
                Ok(())
            }
        }
        TermCheck::Lam(t_c) => {
            if let Type::VPi(ty1, ty2) = ty {
                let mut new_env = c.clone();
                new_env.push_front((Name::Local(i), *ty1));
                type_check(
                    i + 1,
                    c,
                    subst_check(0, TermInfer::Free(Name::Local(i)), *t_c),
                    ty2.call(vfree(Name::Local(i))),
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
        TermInfer::Star => TermInfer::Star,
        TermInfer::Pi(ty1, ty2) => TermInfer::Pi(
            Box::new(subst_check(i, t1.clone(), *ty1)),
            Box::new(subst_check(i, t1, *ty2)),
        ),
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
        Value::VStar => TermCheck::Inf(Box::new(TermInfer::Star)),
        Value::VPi(val, f) => TermCheck::Inf(Box::new(TermInfer::Pi(
            Box::new(quote(i, *val)),
            Box::new(quote(i + 1, f.call(vfree(Name::Quote(i))))),
        ))),
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
