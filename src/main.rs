use std::collections::{BTreeMap, HashMap};
use thiserror::Error;

// E.g. x
pub type Var = String;

// E.g. β
pub type TypeVar = String;

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),   // E.g. 1
    Bool(bool), // E.g. true
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(Var),                          // E.g. x
    Lambda(String, Box<Expr>),         // E.g. λx.x
    App(Box<Expr>, Box<Expr>),         // E.g. (λx.x) 1
    Let(String, Box<Expr>, Box<Expr>), // E.g. let x = 1 in x
    Lit(Lit),                          // E.g. 1 [or] true
    Tuple(Vec<Expr>),                  // E.g. (1, true) [or] (x, y, z)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    TypeVar(TypeVar),            // E.g. β
    Arrow(Box<Type>, Box<Type>), // E.g. int -> int
    Int,                         // E.g. int
    Bool,                        // E.g. bool
    Product(Vec<Type>),          // E.g. int * bool [or] (β₁, β₂, β₃)
}

// E.g. σ := int [or] ∀β.β [or] ∀β₁,β₂.(β₁ * β₂)
#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub quantifier_vars: Vec<TypeVar>, // The "∀β" part of ∀β.(β * int)
    pub inner_type: Type,              // The "(β * int)" part of ∀β.(β * int)
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(name) => write!(f, "{}", name),
            Expr::Lit(Lit::Int(n)) => write!(f, "{}", n),
            Expr::Lit(Lit::Bool(b)) => write!(f, "{}", b),
            Expr::Lambda(param, body) => write!(f, "λ{}.{}", param, body),
            Expr::App(func, arg) => match (func.as_ref(), arg.as_ref()) {
                (Expr::Lambda(_, _), _) => write!(f, "({}) {}", func, arg),
                (_, Expr::App(_, _)) => write!(f, "{} ({})", func, arg),
                (_, Expr::Lambda(_, _)) => write!(f, "{} ({})", func, arg),
                _ => write!(f, "{} {}", func, arg),
            },
            Expr::Let(var, value, body) => {
                write!(f, "let {} = {} in {}", var, value, body)
            }
            Expr::Tuple(exprs) => {
                write!(f, "(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", expr)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::TypeVar(name) => write!(f, "{}", name),
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Arrow(t1, t2) => {
                // Add parentheses around left side if it's an arrow to avoid ambiguity
                match t1.as_ref() {
                    Type::Arrow(_, _) => write!(f, "({}) → {}", t1, t2),
                    _ => write!(f, "{} → {}", t1, t2),
                }
            }
            Type::Product(types) => {
                write!(f, "(")?;
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ty)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TypeScheme {
            quantifier_vars,
            inner_type,
        } = self;

        if quantifier_vars.is_empty() {
            write!(f, "{}", self.inner_type)
        } else {
            write!(f, "forall {}. {}", quantifier_vars.join(" "), inner_type)
        }
    }
}

// E.g. Γ := { x: int, y: ∀β.β }
pub type TypeEnv = BTreeMap<Var, TypeScheme>;

// E.g. S := { (β₁ |-> int), (β₂ |-> β₃) }
pub type Subst = HashMap<TypeVar, Type>;

#[derive(Error, Debug)]
pub enum InferenceError {
    #[error("Variable '{name}' not found in environment")]
    UnboundVariable { name: String },

    #[error("Cannot unify types: expected {expected}, found {actual}")]
    UnificationFailure { expected: Type, actual: Type },

    #[error("Occurs check failed: variable '{var}' occurs in type {ty}")]
    OccursCheck { var: String, ty: Type },

    #[error("Cannot unify tuples of different lengths: {left_len} vs {right_len}")]
    TupleLengthMismatch { left_len: usize, right_len: usize },
}

pub type Result<T> = std::result::Result<T, InferenceError>;

pub struct TypeInference {
    fresh_var_counter: usize,
}

impl Default for TypeInference {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeInference {
    fn new() -> Self {
        Self {
            fresh_var_counter: 0,
        }
    }

    fn fresh_type_var(&mut self) -> TypeVar {
        let type_var = format!("t{}", self.fresh_var_counter);
        self.fresh_var_counter += 1;
        type_var
    }

    fn apply_subst_type(&self, subst: &Subst, ty: &Type) -> Type {
        match ty {
            Type::TypeVar(var) => match subst.get(var) {
                Some(new_var) => new_var.clone(),
                None => ty.clone(),
            },
            Type::Arrow(input_type, output_type) => Type::Arrow(
                Box::new(self.apply_subst_type(subst, input_type)),
                Box::new(self.apply_subst_type(subst, output_type)),
            ),
            Type::Product(types) => Type::Product(
                types
                    .iter()
                    .map(|sub_type| self.apply_subst_type(subst, sub_type))
                    .collect(),
            ),
            Type::Int | Type::Bool => ty.clone(),
        }
    }

    fn apply_subst_scheme(&self, subst: &Subst, type_scheme: &TypeScheme) -> TypeScheme {
        // remove quantifier_vars from substitution
        let mut filtered_subst = subst.clone();
        for type_var in &type_scheme.quantifier_vars {
            filtered_subst.remove(type_var);
        }

        TypeScheme {
            quantifier_vars: type_scheme.quantifier_vars.clone(),
            inner_type: self.apply_subst_type(subst, &type_scheme.inner_type),
        }
    }

    fn apply_subst_env(&self, subst: &Subst, env: &TypeEnv) -> TypeEnv {
        env.iter()
            .map(|(var, type_scheme)| (var.clone(), self.apply_subst_scheme(subst, type_scheme)))
            .collect()
    }

    fn compose_subst(&self, subst1: &Subst, subst2: &Subst) -> Subst {
        let mut result_subst = subst1.clone();

        for (from_type_var, to_type) in subst2 {
            result_subst.insert(
                from_type_var.clone(),
                self.apply_subst_type(subst1, to_type),
            );
        }

        result_subst
    }

    fn 
}

fn main() {
    println!("Hello, world!");
}
