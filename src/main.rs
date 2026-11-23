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
    Pi(String, Box<Term>, Box<Term>),     // (x: Nat) -> Nat
    Lambda(String, Box<Term>, Box<Term>), // fun (x : Nat) => x
    Let(Box<Term>, Box<Term>, Box<Term>),
}

#[derive(Clone, Debug)]
struct RecursorRule(String, usize, Term);

#[derive(Debug, Clone)]
enum ConstantInfo { // lean4
    Definition(Term, Term),
    Theorem(Term, Term),
    Inductive(Term, Vec<(String, Term)>),
    Constructor(Term, String, usize), // idxed by name
    Recursor(Term, usize, Vec<RecursorRule>),
}

impl ConstantInfo {
    fn ty(&self) -> &Term {
        match self {
            ConstantInfo::Definition(ty, _) => ty,
            ConstantInfo::Theorem(ty, _) => ty,
            ConstantInfo::Inductive(ty, _) => ty,
            ConstantInfo::Constructor(ty, _, _) => ty,
            ConstantInfo::Recursor(ty, _, _) => ty,
        }
    }
}

fn sym(s: &'_ str) -> impl Parser<'_, &'_ str, &'_ str, extra::Err<Simple<'_, char>>> + Clone {
    just(s).padded()
}

fn kwd(s: &'_ str) -> impl Parser<'_, &'_ str, &'_ str, extra::Err<Simple<'_, char>>> + Clone {
    keyword(s).padded()
}

fn ident<'a>() -> impl Parser<'a, &'a str, String, extra::Err<Simple<'a, char>>> + Clone {
    text::ident()
        .filter(|x| {
            *x != "def" && *x != "fun" && *x != "theorem" && *x != "Type" && *x != "inductive"
        })
        .padded()
        .map(|s: &str| s.to_string())
}

fn unpack(is_pi: bool, binders: Vec<(Vec<String>, Term)>, body: Term) -> Term { // i hate this is pattern
    binders
        .into_iter()
        .rev()
        .flat_map(|(names, ty)| names.into_iter().rev().map(move |n| (n, ty.clone())))
        .fold(body, |acc, (name, ty)| {
            let (ty, body) = (Box::new(ty), Box::new(acc));
            if is_pi {
                Term::Pi(name, ty, body)
            } else {
                Term::Lambda(name, ty, body)
            }
        })
}

fn term<'a>() -> impl Parser<'a, &'a str, Term, extra::Err<Simple<'a, char>>> {
    recursive(|term| {
        let binder = ident()
            .repeated()
            .at_least(1)
            .collect::<Vec<_>>()
            .then_ignore(sym(":"))
            .then(term.clone())
            .delimited_by(sym("("), sym(")"));
        let binders = binder.repeated().at_least(1).collect::<Vec<_>>();

        let lambda = kwd("fun")
            .ignore_then(binders.clone())
            .then_ignore(sym("=>"))
            .then(term.clone())
            .map(|(binders, body)| unpack(false, binders, body));

        let pi_ = binders
            .then_ignore(sym("->"))
            .then(term.clone())
            .map(|(binders, body)| unpack(true, binders, body));

        let atom = choice((
            kwd("Type").to(Term::Universe(0)),
            ident().map(Term::Global),
            term.clone().delimited_by(sym("("), sym(")")),
        ));

        let call = atom.clone().foldl(atom.repeated(), |f, a| call(f, a));

        let arrow = call
            .then(sym("->").ignore_then(term).or_not())
            .map(|(a, b)| match b {
                Some(b) => pi(String::new(), a, b),
                None => a,
            });
        choice((lambda, pi_, arrow))
    })
}

fn gen_indices(term: Term, indices: &mut Vec<String>) -> Term { // this is so hacky, it should be two seperate types
    match term {
        Term::Global(name) => indices
            .iter()
            .rev()
            .position(|n| n == &name)
            .map_or(Term::Global(name), |i| Term::Var(i)),
        Term::Call(f, a) => call(gen_indices(*f, indices), gen_indices(*a, indices)),
        Term::Pi(name, ty, body) => {
            let ty = gen_indices(*ty, indices);
            indices.push(name.clone());
            let body = gen_indices(*body, indices);
            indices.pop();
            pi(name.clone(), ty, body)
        }
        Term::Lambda(name, ty, body) => {
            let ty = gen_indices(*ty, indices);
            indices.push(name.clone());
            let body = gen_indices(*body, indices);
            indices.pop();
            lambda(name.clone(), ty, body)
        }
        //Term::Let(_, _, _) => {}
        _ => term.clone(),
    }
}

fn parser<'src>()
-> impl Parser<'src, &'src str, Vec<(String, ConstantInfo)>, extra::Err<Simple<'src, char>>> {
    choice((
        choice((kwd("def").to(false), kwd("theorem").to(true)))
            .then(ident())
            .then_ignore(sym(":"))
            .then(term())
            .then_ignore(sym(":="))
            .then(term())
            .map(|(((is_theorem, name), ty), value)| {
                if is_theorem {
                    (
                        name,
                        ConstantInfo::Theorem(
                            gen_indices(ty, &mut Vec::new()),
                            gen_indices(value, &mut Vec::new()),
                        ),
                    )
                } else {
                    (
                        name,
                        ConstantInfo::Definition(
                            gen_indices(ty, &mut Vec::new()),
                            gen_indices(value, &mut Vec::new()),
                        ),
                    )
                }
            }),
        kwd("inductive")
            .ignore_then(ident())
            .then_ignore(sym(":"))
            .then(term())
            .then_ignore(sym(":="))
            .then(
                sym("|")
                    .ignore_then(ident().then_ignore(sym(":")).then(term()))
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map(|((name, ty), branches)| {
                (
                    name,
                    ConstantInfo::Inductive(
                        ty,
                        branches
                            .into_iter()
                            .map(|(name, term)| (name, gen_indices(term, &mut Vec::new())))
                            .collect(),
                    ),
                )
            }),
    ))
    .repeated()
    .collect()
    .then_ignore(end())
}

struct Environment {
    constants: HashMap<String, ConstantInfo>,
}

fn shift(term: Term, amount: isize, depth: usize) -> Term {
    match term {
        Term::Var(i) if i >= depth => Term::Var((i as isize + amount) as usize),
        Term::Lambda(name, ty, body) => lambda(
            name,
            shift(*ty, amount, depth),
            shift(*body, amount, depth + 1),
        ),
        Term::Pi(name, ty, body) => pi(
            name,
            shift(*ty, amount, depth),
            shift(*body, amount, depth + 1),
        ),
        Term::Call(f, a) => call(shift(*f, amount, depth), shift(*a, amount, depth)),
        _ => term,
    }
}

fn real_substitute(term: Term, index: usize, replacement: Term) -> Term {
    match term {
        Term::Var(i) if i == index => replacement,
        Term::Lambda(name, ty, body) => lambda(
            name,
            real_substitute(*ty, index, replacement.clone()),
            real_substitute(*body, index + 1, shift(replacement, 1, 0)),
        ),
        Term::Pi(name, ty, body) => pi(
            name,
            real_substitute(*ty, index, replacement.clone()),
            real_substitute(*body, index + 1, shift(replacement, 1, 0)),
        ),
        Term::Call(f, a) => call(
            real_substitute(*f, index, replacement.clone()),
            real_substitute(*a, index, replacement),
        ),
        _ => term.clone(),
    }
}

fn substitute(term: Term, replacement: Term) -> Term {
    shift(real_substitute(term, 0, shift(replacement, 1, 0)), -1, 0)
}

fn reduce(env: &Environment, term: Term) -> Term {
    match term {
        Term::Call(_, _) => {
            let (f, args) = unroll_call(term);
            let rf = reduce(env, f);

            if let Term::Lambda(_, _, body) = rf { // beta
                let mut iter = args.into_iter();
                return reduce(env, apply(substitute(*body, iter.next().unwrap()), iter));
            } else if let Term::Global(ref name) = rf { // iota
                if let Some(ConstantInfo::Recursor(_, num_minors, rules)) = env.constants.get(name)
                {
                    let i = 1 + num_minors;
                    if args.len() > i {
                        let (f, bargs) = unroll_call(reduce(env, args[i].clone()));
                        if let Term::Global(ref name) = f {
                            if let Some(rule) =
                                rules.iter().find(|r| &r.0 == name && r.1 == bargs.len())
                            {
                                let mut new_args = args[..i].to_vec();
                                new_args.extend(bargs);
                                new_args.extend(args[i + 1..].iter().cloned());
                                return reduce(env, apply(rule.2.clone(), new_args));
                            }
                        }
                    }
                }
            }
            apply(rf, args)
        }
        Term::Global(ref name)
            if let Some(ConstantInfo::Definition(_, value)) = env.constants.get(name) => // delta // i had to update rust for this
        {
            reduce(env, value.clone())
        }
        _ => term,
    }
}

fn equal(env: &Environment, a: &Term, b: &Term) -> bool { // alpha equivalence
    match (reduce(env, a.clone()), reduce(env, b.clone())) {
        (Term::Var(i), Term::Var(j)) => i == j,
        (Term::Universe(i), Term::Universe(j)) => i == j,
        (Term::Global(a), Term::Global(b)) => a == b,
        (Term::Literal(a), Term::Literal(b)) => a == b,
        (Term::Call(f1, a1), Term::Call(f2, a2)) => equal(env, &f1, &f2) && equal(env, &a1, &a2),
        (Term::Pi(_, t1, b1), Term::Pi(_, t2, b2)) => equal(env, &t1, &t2) && equal(env, &b1, &b2),
        (Term::Lambda(_, t1, b1), Term::Lambda(_, t2, b2)) => {
            equal(env, &t1, &t2) && equal(env, &b1, &b2)
        }
        _ => false,
    }
}

fn add_declaration(
    env: &mut Environment,
    name: String,
    constant: ConstantInfo,
) -> Result<(), TypeError> {
    let mut context = Vec::new();
    match constant {
        ConstantInfo::Definition(ty, value) => {
            get_universe(env, &mut context, &ty)?;
            check(env, &mut context, &value, &ty)?;
            env.constants.insert(
                name.clone(),
                ConstantInfo::Definition(reduce(env, ty), reduce(env, value)),
            );
        }
        ConstantInfo::Inductive(ty, branches) => {
            get_universe(env, &mut context, &ty)?;
            env.constants.insert(
                name.clone(),
                ConstantInfo::Inductive(ty.clone(), branches.clone()),
            );
            for (bname, ty) in &branches { // i love shadowing
                get_universe(env, &mut context, ty)?;
                env.constants.insert(
                    bname.clone(),
                    ConstantInfo::Constructor(
                        ty.clone(),
                        name.clone(),
                        unroll_pi(ty.clone()).len(),
                    ),
                );
            }

            env.constants
                .insert(name.clone() + "_rec", gen_recursor(&name, &branches));
        }
        ConstantInfo::Theorem(ty, value) => {
            get_universe(env, &mut context, &ty)?;
            check(env, &mut context, &value, &ty)?;
            env.constants.insert(
                name.clone(),
                ConstantInfo::Theorem(reduce(env, ty), reduce(env, value)),
            );
        }
        _ => {
            unreachable!()
        } // #goodcode
    }
    Ok(())
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

fn get_universe(
    env: &Environment,
    context: &mut Vec<Term>,
    term: &Term,
) -> Result<usize, TypeError> {
    match reduce(env, infer(env, context, term)?) {
        Term::Universe(i) => Ok(i),
        _ => Err(TypeError::DidntReduce),
    }
}

fn check(
    env: &Environment,
    context: &mut Vec<Term>,
    term: &Term,
    expected: &Term,
) -> Result<(), TypeError> {
    let expected = reduce(env, expected.clone());
    if let (Term::Lambda(_, ty, body), Term::Pi(_, exp_ty, exp_ret)) = (term, &expected) {
        // check if lambda and pi are same
        get_universe(env, context, ty)?;
        if !equal(env, ty, exp_ty) {
            return Err(TypeError::Unequal(*ty.clone(), *exp_ty.clone()));
        }
        context.push((**ty).clone());
        let result = check(env, context, body, exp_ret);
        context.pop();
        return result;
    }

    let term = infer(env, context, term)?;
    if !equal(env, &term, &expected) {
        return Err(TypeError::Unequal(term, expected));
    }
    Ok(())
}

fn infer(env: &Environment, context: &mut Vec<Term>, term: &Term) -> Result<Term, TypeError> {
    match term {
        Term::Var(i) => {
            if i >= &context.len() {
                Err(TypeError::FreeVariable)
            } else {
                Ok(shift(
                    context[context.len() - 1 - i].clone(),
                    (i + 1) as isize,
                    0,
                )) // stack
            }
        }
        Term::Universe(i) => Ok(Term::Universe(i + 1)),
        Term::Global(name) => env
            .constants
            .get(name)
            .map(|info| info.ty().clone())
            .ok_or(TypeError::NoGlobal),
        Term::Call(f, a) => {
            let f_ty = reduce(env, infer(env, context, f)?);
            if let Term::Pi(_, arg_ty, ret_ty) = f_ty {
                check(env, context, a, &arg_ty)?;
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
        Term::Lambda(name, ty, body) => {
            get_universe(env, context, ty)?; // make sure is type
            context.push(*ty.clone());
            let body = infer(env, context, body)?;
            context.pop();
            Ok(lambda(name.clone(), *ty.clone(), body))
        }
        _ => Err(TypeError::Unsupported),
    }
}

fn unroll_pi(mut term: Term) -> Vec<(String, Term)> {
    let mut fields = Vec::new();
    while let Term::Pi(name, field_ty, body) = term {
        fields.push((name, *field_ty));
        term = *body;
    }
    fields
}

fn unroll_call(mut term: Term) -> (Term, Vec<(Term)>) {
    let mut args = Vec::new();
    while let Term::Call(f, a) = term {
        args.push(*a);
        term = *f;
    }
    args.reverse();
    (term, args)
}

fn compile_rule(rec_name: &str, num_minors: usize, i: usize, recursive: Vec<bool>) -> Term {
    let mut body = Term::Var(recursive.len() + (num_minors - 1 - i));

    for (j, &is_rec) in recursive.iter().enumerate() {
        let field = Term::Var(recursive.len() - 1 - j);
        body = call(body, field.clone());
        if is_rec {
            let mut args = Vec::new();
            args.push(Term::Var(recursive.len() + num_minors));
            for i in 0..num_minors {
                args.push(Term::Var(recursive.len() + (num_minors - 1 - i)));
            }
            args.push(field);
            body = call(body, apply(Term::Global(rec_name.to_string()), args));
        }
    }

    for _ in (0..recursive.len()).rev() {
        body = lambda(String::new(), Term::Universe(0), body);
    }
    for _ in (0..num_minors).rev() {
        body = lambda(String::new(), Term::Universe(0), body);
    }
    lambda(String::new(), Term::Universe(0), body)
}

fn call(f: Term, a: Term) -> Term {
    Term::Call(Box::new(f), Box::new(a))
}
fn pi(name: String, ty: Term, body: Term) -> Term {
    Term::Pi(name, Box::new(ty), Box::new(body))
}
fn lambda(name: String, ty: Term, body: Term) -> Term {
    Term::Lambda(name, Box::new(ty), Box::new(body))
}
fn apply(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
    args.into_iter().fold(f, call)
}

fn gen_recursor(ind: &str, branches: &Vec<(String, Term)>) -> ConstantInfo {
    let mut ty = pi(
        "x".to_string(),
        Term::Global(ind.to_string()),
        call(Term::Var(branches.len() + 1), Term::Var(0)),
    );
    let all_fields: Vec<Vec<(String, Term)>> = branches
        .iter()
        .map(|(_, ty)| unroll_pi(ty.clone()))
        .collect();

    let mut rules = Vec::with_capacity(branches.len());
    for (i, ((name, _), fields)) in branches.iter().zip(&all_fields).enumerate().rev() {
        // minor premises this naming scheme is very confusing
        let recursive: Vec<bool> = fields
            .iter()
            .map(|(_, ty)| match ty {
                Term::Global(name) => name == ind,
                _ => false,
            })
            .collect();
        let mut j = i;

        let mut binders = Vec::new();
        let mut binder_offsets = Vec::new();

        //  motive ctor fields ctor
        for (i, (name, ty)) in fields.into_iter().enumerate() {
            binder_offsets.push(binders.len());
            binders.push((name.clone(), ty.clone()));
            j += 1;

            if recursive[i] {
                let ty = call(Term::Var(j), Term::Var(0)); // induction hypothesis, built backwards
                binders.push(("ih".to_string(), ty));
                j += 1;
            }
        }

        let fields: Vec<Term> = binder_offsets
            .iter()
            .map(|&i| Term::Var(binders.len() - 1 - i))
            .collect();

        let mut minor_ty = call(
            Term::Var(j),
            apply(Term::Global(name.clone()), fields.clone()),
        );
        for (name, ty) in binders.into_iter().rev() {
            minor_ty = pi(name.clone(), ty.clone(), minor_ty);
        }

        ty = pi(String::new(), minor_ty, ty);

        rules.push(RecursorRule(
            name.clone(),
            fields.len(),
            compile_rule(&*(ind.to_owned() + "_rec"), branches.len(), i, recursive),
        ));
    }

    rules.reverse();

    ty = pi(
        String::new(),
        pi(
            String::new(),
            Term::Global(ind.to_string()),
            Term::Universe(0),
        ),
        ty,
    );
    ConstantInfo::Recursor(ty, branches.len(), rules)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut s = String::new();
    File::open("variable.pv")?.read_to_string(&mut s)?;
    s = s.replace("→", "->");
    let parser = parser();
    let declarations = parser.parse(s.as_str()).into_result().unwrap(); // fuck you
    let mut env = Environment {
        constants: HashMap::new(),
    };
    for (name, declaration) in declarations {
        add_declaration(&mut env, name, declaration)?;
    }
    Ok(())
}
