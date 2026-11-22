use chumsky::prelude::*;
use chumsky::text::keyword;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::fs::File;
use std::io::Read;

#[derive(Clone, Debug, PartialEq)]
enum Literal {
    Number(usize),
    String(String),
}

#[derive(Clone, Debug)]
enum Term {
    Var(usize), // index
    Universe(usize),
    Global(String),
    Literal(Literal),
    Call(Box<Term>, Box<Term>),
    Pi(String, Box<Term>, Box<Term>), // (x: Nat) -> Nat
    Lambda(String, Box<Term>, Box<Term>), // fun (x : Nat) => x
    Let(Box<Term>, Box<Term>, Box<Term>),
}

#[derive(Debug, Clone)]
enum Declaration {
    Definition(String, Term, Term),
    Theorem(String, Term, Term),
}

fn sym(s: &'_ str) -> impl Parser<'_, &'_ str, &'_ str, extra::Err<Simple<'_, char>>> + Clone {
    just(s).padded()
}

fn kwd(s: &'_ str) -> impl Parser<'_, &'_ str, &'_ str, extra::Err<Simple<'_, char>>> + Clone {
    keyword(s).padded()
}


fn ident<'a>() -> impl Parser<'a, &'a str, String, extra::Err<Simple<'a, char>>> + Clone {
    text::ident().filter(|x| *x != "def" && *x != "fun" && *x != "theorem" && *x != "Type").padded().map(|s: &str| s.to_string())
}

fn unpack(is_pi: bool, binders: Vec<(Vec<String>, Term)>, body: Term) -> Term { // i hate this is pattern
    binders
        .into_iter()
        .rev()
        .flat_map(|(names, ty)| names.into_iter().rev().map(move |n| (n, ty.clone())))
        .fold(body, |acc, (name, ty)| {
            let (ty, body) = (Box::new(ty), Box::new(acc));
            if is_pi { Term::Pi (name, ty, body) } else { Term::Lambda (name, ty, body) }
        })
}

fn term<'a>() -> impl Parser<'a, &'a str, Term, extra::Err<Simple<'a, char>>> {
    recursive(|term| {
        let binder = ident().repeated().at_least(1).collect::<Vec<_>>().then_ignore(sym(":")).then(term.clone()).delimited_by(sym("("), sym(")"));
        let binders = binder.repeated().at_least(1).collect::<Vec<_>>();

        let lambda = kwd("fun").ignore_then(binders.clone()).then_ignore(sym("=>")).then(term.clone()) .map(|(binders, body)| unpack(false, binders, body));

        let pi = binders.then_ignore(sym("->")).then(term.clone())
            .map(|(binders, body)| unpack(true, binders, body));

        let atom = choice((
            kwd("Type").to(Term::Universe(0)),
            ident().map(Term::Global),
            term.clone().delimited_by(sym("("), sym(")")),
        ));

        let call = atom.clone().foldl(atom.repeated(), |f, a| Term::Call(Box::new(f), Box::new(a)));

        let arrow = call
            .then(sym("->").ignore_then(term).or_not())
            .map(|(a, b)| match b {
                Some(b) => Term::Pi(String::new(), Box::new(a), Box::new(b)),
                None => a,
            });
            choice((lambda, pi, arrow))
    })
}

fn gen_indices(term: Term, indices: &mut Vec<String>) -> Term { // this is so hacky, it should be two seperate types
    match term {
        Term::Global(name) => {
            indices.iter().rev().position(|n| n == &name).map_or(Term::Global(name), |i| Term::Var(i))
        }
        Term::Call(f, a) => {
            Term::Call(Box::new(gen_indices(*f, indices)), Box::new(gen_indices(*a, indices)))
        }
        Term::Pi(name, ty, body) => {
            let ty = gen_indices(*ty, indices);
            indices.push(name.clone());
            let body = gen_indices(*body, indices);
            indices.pop();
            Term::Pi(name.clone(), Box::from(ty), Box::from(body))
        }
        Term::Lambda(name, ty, body) => {
            let ty = gen_indices(*ty, indices);
            indices.push(name.clone());
            let body = gen_indices(*body, indices);
            indices.pop();
            Term::Lambda(name.clone(), Box::from(ty), Box::from(body))
        }
        //Term::Let(_, _, _) => {}
        _ => { term.clone() }
    }
}

fn parser<'src>() -> impl Parser<'src, &'src str, Vec<Declaration>, extra::Err<Simple<'src, char>>> {
    choice((kwd("def").to(false), kwd("theorem").to(true)))
        .then(ident())
        .then_ignore(sym(":"))
        .then(term())
        .then_ignore(sym(":="))
        .then(term())
        .map(|(((is_theorem, name), ty), value)| {
            if is_theorem {
                Declaration::Theorem(name, gen_indices(ty, &mut Vec::new()), gen_indices(value, &mut Vec::new()))
            } else {
                Declaration::Definition(name, gen_indices(ty, &mut Vec::new()), gen_indices(value, &mut Vec::new()))
            }
        }).repeated().collect().then_ignore(end())
}

struct Environment {
    definitions: HashMap<String, Declaration>,
}

fn shift(term: Term, amount: isize, depth: usize) -> Term {
    match term {
        Term::Var(i) if i >= depth => Term::Var((i as isize + amount) as usize),
        Term::Lambda(name, ty, body) => Term::Lambda(name, Box::new(shift(*ty, amount, depth)), Box::new(shift(*body, amount, depth + 1))),
        Term::Pi(name, ty, body) => Term::Pi(name, Box::new(shift(*ty, amount, depth)), Box::new(shift(*body, amount, depth + 1))),
        Term::Call(f, a) => Term::Call(Box::new(shift(*f, amount, depth)), Box::new(shift(*a, amount, depth))),
        _ => term,
    }
}

fn real_substitute(term: Term, index: usize, replacement: Term) -> Term {
    match term {
        Term::Var(i) if i == index => replacement,
        Term::Lambda(name, ty, body) => { Term::Lambda(name, Box::new(real_substitute(*ty, index, replacement.clone())), Box::new(real_substitute(*body, index + 1, shift(replacement, 1, 0)))) }
        Term::Pi(name, ty, body) => { Term::Pi(name, Box::new(real_substitute(*ty, index, replacement.clone())), Box::new(real_substitute(*body, index + 1, shift(replacement, 1, 0)))) }
        Term::Call(f, a) => { Term::Call(Box::new(real_substitute(*f, index, replacement.clone())), Box::new(real_substitute(*a, index, replacement))) }
        _ => { term.clone() }
    }
}

fn substitute(term: Term, replacement: Term) -> Term {
    shift(real_substitute(shift(term, 0, 0), 0, replacement), -1, 0)
}

fn reduce(env: &Environment, term: Term) -> Term {
    match term {
        Term::Call(f, a) => { // beta
            let rf = reduce(env, *f);
            if let Term::Lambda(name, ty, body) = rf {
                reduce(env, substitute(*body, *a))
            } else {
                Term::Call(Box::new(rf), a)
            }
        },
        Term::Global(ref name) => { // delta
            if let Some(Declaration::Definition(_, _, val)) = env.definitions.get(name) {
                reduce(env, val.clone())
            } else {
                term
            }
        }
        _ => term
    }
}



fn equal(env: &Environment, a: &Term, b: &Term) -> bool { // alpha equivalence
    match (reduce(env, a.clone()), reduce(env, b.clone())) {
        (Term::Var(i), Term::Var(j)) => i == j,
        (Term::Universe(i), Term::Universe(j)) => i == j,
        (Term::Global(a), Term::Global(b)) => a == b,
        (Term::Literal(a), Term::Literal(b)) => a == b,
        (Term::Call(f1, a1), Term::Call(f2, a2)) => equal(env, &f1, &f2) && equal(env, &a1, &a2),
        (Term::Pi(n1, t1, b1), Term::Pi(n2, t2, b2)) => equal(env, &t1, &t2) && equal(env, &b1, &b2),
        (Term::Lambda(n1, t1, b1), Term::Lambda(n2, t2, b2)) => equal(env, &t1, &t2) && equal(env, &b1, &b2),
        _ => false,
    }
}

fn add_declaration(env: &mut Environment, declaration: Declaration) -> Result<(), TypeError> {
    let mut context = Vec::new();
    match declaration {
        Declaration::Definition(name, ty, value) => {
            get_universe(env, &mut context, &ty)?;
            check(env, &mut context, &value, &ty)?;
            env.definitions.insert(name.clone(), Declaration::Definition(name, reduce(env, ty), reduce(env, value)));
        }
        _ => {

        }
    }Ok(())
}

#[derive(Debug)]
enum TypeError {
    Unsupported,
    FreeVariable,
    NoGlobal,
    DidntReduce,
    Unequal(Term, Term),
}


impl Display for TypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            _ => write!(f, "{:?}", self),
        }
    }
}

impl std::error::Error for TypeError {}

fn get_universe(env: &Environment, context: &mut Vec<Term>, term: &Term) -> Result<usize, TypeError> {
    match infer(env, context, term)? {
        Term::Universe(i) => Ok(i),
        _ => Err(TypeError::DidntReduce),
    }
}

fn check(env: &Environment, context: &mut Vec<Term>, term: &Term, expected: &Term) -> Result<(), TypeError> {
    let expected = reduce(env, expected.clone());
    if let (Term::Lambda(_, ty, body), Term::Pi(_, exp_ty, exp_ret)) = (term, &expected) { // check if lambda and pi are same
        get_universe(env, context, ty)?;
        if !equal(env, ty, exp_ty) {
            return Err(TypeError::Unequal(*ty.clone(), *exp_ty.clone()))
        }
        context.push((**ty).clone());
        let result = check(env, context, body, exp_ret);
        context.pop();
        return result;
    }

    let term = infer(env, context, term)?;
    if !equal(env, &term, &expected) {
        return Err(TypeError::Unequal(term, expected))
    }
    Ok(())
}

fn infer(env: &Environment, context: &mut Vec<Term>, term: &Term) -> Result<Term, TypeError> {
    match term {
        Term::Var(i) => {
            if i >= &context.len() {
                Err(TypeError::FreeVariable)
            } else {
                Ok(shift(context[context.len() - 1 - i].clone(), (i + 1) as isize, 0)) // stack
            }
        }
        Term::Universe(i) => Ok(Term::Universe(i + 1)),
        Term::Global(name) => {
            if let Some(Declaration::Definition(_, ty, _)) = env.definitions.get(name) {
                Ok(ty.clone())
            } else {
                Err(TypeError::NoGlobal)
            }
        }
        Term::Call(f, a) => {
            let f_ty = reduce(env, infer(env, context, f)?);
            if let Term::Pi(_, param_ty, ret_ty) = f_ty {
                check(env, context, a, &param_ty)?;
                Ok(substitute(*ret_ty, *a.clone()))
            } else {
                Err(TypeError::DidntReduce)
            }
        }
        Term::Pi(_, ty, body) => {
            let i = get_universe(env, context, ty)?;
            context.push(*ty.clone());
            let j = get_universe(env, context, body)?;
            context.pop();
            Ok(Term::Universe(i.max(j)))
        }
        Term::Lambda(n, ty, body) => {
            get_universe(env, context, ty)?; // make sure is type
            context.push(*ty.clone());
            let body = infer(env, context, body)?;
            context.pop();
            Ok(Term::Pi(n.clone(), ty.clone(), Box::new(body)))
        }
        _ => Err(TypeError::Unsupported),
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    File::open("variable.pv")?.read_to_string(&mut s)?;
    s = s.replace("→", "->");
    let parser = parser();
    let declarations = parser.parse(s.as_str()).into_result().unwrap(); // fuck you
    for declaration in declarations {
        add_declaration(&mut Environment { definitions: HashMap::new() }, declaration)?;
    }
    Ok(())
}
