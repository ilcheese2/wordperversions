use std::fs::File;
use std::io::Read;
use chumsky::prelude::*;
use chumsky::text::keyword;

#[derive(Clone, Debug)]
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
    text::ident().padded().map(|s: &str| s.to_string())
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
    definitions: std::collections::HashMap<String, Term>,
}

fn shift(term: Term, amount: isize) -> Term {
    match term {
        Term::Var(i) => Term::Var((i as isize + amount) as usize),
        Term::Lambda(name, ty, body) => Term::Lambda(name, Box::new(shift(*ty, amount)), Box::new(shift(*body, amount))),
        Term::Pi(name, ty, body) => Term::Pi(name, Box::new(shift(*ty, amount)), Box::new(shift(*body, amount))),
        Term::Call(f, a) => Term::Call(Box::new(shift(*f, amount)), Box::new(shift(*a, amount))),
        _ => term,
    }
}

fn real_substitute(term: Term, index: usize, replacement: Term) -> Term {
    match term {
        Term::Var(i) if i == index => replacement,
        Term::Lambda(name, ty, body) => { Term::Lambda(name, Box::new(real_substitute(*ty, index, replacement.clone())), Box::new(real_substitute(*body, index + 1, shift(replacement, 1)))) }
        Term::Pi(name, ty, body) => { Term::Pi(name, Box::new(real_substitute(*ty, index, replacement.clone())), Box::new(real_substitute(*body, index + 1, shift(replacement, 1)))) }
        Term::Call(f, a) => { Term::Call(Box::new(real_substitute(*f, index, replacement.clone())), Box::new(real_substitute(*a, index, replacement))) }
        _ => { term.clone() }
    }
}

fn substitute(term: Term, replacement: Term) -> Term {
    shift(real_substitute(shift(term, 0), 0, replacement), -1)
}

fn reduce(env: &Environment, term: Term) -> Term {
    match term {
        Term::Call(f, a) => { // beta
            let rf = reduce(env, *f);
            if let Term::Lambda(name, ty, body) = rf {
                reduce(env, substitute(*body, *a))
            } else {
                Term::Call(Box::new(rf), Box::new(*a))
            }
        },
        Term::Global(name) => { // delta
            if env.definitions.contains_key(&name) {
                reduce(env, env.definitions.get(&name).unwrap().clone())
            } else {
                Term::Global(name)
            }
        }
        _ => {
            term
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    File::open("variable.pv")?.read_to_string(&mut s)?;
    s = s.replace("→", "->");
    let parser = parser();
    let declarations = parser.parse(s.as_str()).into_result().unwrap(); // fuck you
    Ok(())
}
