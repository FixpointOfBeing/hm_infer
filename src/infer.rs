use crate::ast::*;
use std::collections::{HashMap, HashSet};
use std::fmt;

pub type Subst = HashMap<String, Type>;

pub type TypeEnv = HashMap<String, TypeScheme>;

#[derive(Debug, Clone, PartialEq)]
pub enum InferError {
    UnificationFail(Type, Type),
    InfiniteType(String, Type),
    UnboundVariable(String),
    UnexpectedType(Type),
}

impl std::fmt::Display for InferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InferError::UnificationFail(t1, t2) => {
                write!(f, "Unification failed between types: {} and {}", t1, t2)
            }
            InferError::InfiniteType(name, ty) => {
                write!(f, "Infinite type detected: {} occurs in {}", name, ty)
            }
            InferError::UnboundVariable(name) => write!(f, "Unbound variable: {}", name),
            InferError::UnexpectedType(ty) => write!(f, "Unexpected type: {}", ty),
        }
    }
}

pub struct TypeInfer {
    counter: usize,
}
impl TypeInfer {
    pub fn new() -> Self {
        TypeInfer { counter: 0 }
    }

    fn fresh_type_var(&mut self) -> Type {
        let var_name = format!("t{}", self.counter);
        self.counter += 1;
        Type::TyVar(var_name)
    }

    pub fn infer(&mut self, env: &TypeEnv, expr: &Expr) -> Result<(Subst, Type), InferError> {
        match expr {
            Expr::Nat(_) => Ok((Subst::new(), Type::TyNat)),
            Expr::Bool(_) => Ok((Subst::new(), Type::TyBool)),
            Expr::If(pred, conseq, alt) => {
                let mut curr_env = env.clone();

                let (subst1, pred_ty) = self.infer(&curr_env, pred)?;
                curr_env = self.apply_subst_env(&subst1, &curr_env);

                let (subst2, conseq_ty) = self.infer(&curr_env, conseq)?;
                curr_env = self.apply_subst_env(&subst2, &curr_env);

                let (subst3, alt_ty) = self.infer(&curr_env, alt)?;
                self.apply_subst_env(&subst3, &curr_env);

                let subst4 = self.unify(&pred_ty, &Type::TyBool)?;
                let subst5 = self.unify(&conseq_ty, &alt_ty)?;

                let subst6 = self.compose_substs(vec![&subst5, &subst4, &subst3, &subst2, &subst1]);
                let ty = self.apply_subst(&subst6, &conseq_ty);

                Ok((subst6, ty))
            }
            Expr::IsZero(expr1) => {
                let (subst1, ty) = self.infer(env, expr1)?;
                let subst2 = self.unify(&ty, &Type::TyNat)?;
                let subst3 = self.compose_subst(&subst2, &subst1);
                Ok((subst3, Type::TyBool))
            }
            Expr::Succ(expr1) => {
                let (subst1, ty) = self.infer(env, expr1)?;
                let subst2 = self.unify(&ty, &Type::TyNat)?;
                let subst3 = self.compose_subst(&subst2, &subst1);
                Ok((subst3, Type::TyNat))
            }
            Expr::Pair(fst, snd) => {
                let mut curr_env = env.clone();
                let (subst1, fst_ty) = self.infer(&curr_env, fst)?;
                curr_env = self.apply_subst_env(&subst1, &curr_env);
                let (subst2, snd_ty) = self.infer(&curr_env, snd)?;
                let subst3 = self.compose_subst(&subst2, &subst1);
                let fst_ty_final = self.apply_subst(&subst3, &fst_ty);
                let snd_ty_final = self.apply_subst(&subst3, &snd_ty);
                Ok((
                    subst3,
                    Type::TyPair(Box::new(fst_ty_final), Box::new(snd_ty_final)),
                ))
            }
            Expr::PairFst(pair) => {
                let (subst1, ty) = self.infer(env, pair)?;
                let fst_ty = self.fresh_type_var();
                let snd_ty = self.fresh_type_var();
                let subst2 = self.unify(
                    &ty,
                    &Type::TyPair(Box::new(fst_ty.clone()), Box::new(snd_ty)),
                )?;
                let subst3 = self.compose_subst(&subst2, &subst1);
                let fst_ty1 = self.apply_subst(&subst3, &fst_ty);
                Ok((subst3, fst_ty1))
            }
            Expr::PairSnd(pair) => {
                let (subst1, ty) = self.infer(env, pair)?;
                let fst_ty = self.fresh_type_var();
                let snd_ty = self.fresh_type_var();
                let subst2 = self.unify(
                    &ty,
                    &Type::TyPair(Box::new(fst_ty), Box::new(snd_ty.clone())),
                )?;
                let subst3 = self.compose_subst(&subst2, &subst1);
                let snd_ty1 = self.apply_subst(&subst3, &snd_ty);
                Ok((subst3, snd_ty1))
            }
            Expr::Var(name) => match env.get(name) {
                Some(scheme) => {
                    let instantiated = self.instantiate(scheme);
                    Ok((Subst::new(), instantiated))
                }
                None => Err(InferError::UnboundVariable(name.to_string())),
            },
            Expr::Lambda(param, body) => {
                let param_ty = self.fresh_type_var();
                let mut env1 = env.clone();
                env1.insert(
                    param.to_string(),
                    TypeScheme {
                        vars: vec![],
                        ty: param_ty.clone(),
                    },
                );
                let (subst, body_ty) = self.infer(&env1, &body)?;
                let param_ty_subst = self.apply_subst(&subst, &param_ty);
                let res_ty = Type::TyArrow(Box::new(param_ty_subst), Box::new(body_ty));
                Ok((subst, res_ty))
            }
            Expr::App(fun, arg) => {
                let (subst1, func_ty) = self.infer(env, fun)?;
                let env1 = self.apply_subst_env(&subst1, env);
                let (subst2, arg_ty) = self.infer(&env1, arg)?;
                let func_ty_subst = self.apply_subst(&subst2, &func_ty);
                let res_ty = self.fresh_type_var();
                let expected_func_ty = Type::TyArrow(Box::new(arg_ty), Box::new(res_ty.clone()));
                let subst3 = self.unify(&func_ty_subst, &expected_func_ty)?;
                let subst4 = self.compose_subst(&subst3, &self.compose_subst(&subst2, &subst1));
                let res_ty_subst4 = self.apply_subst(&subst4, &res_ty);
                Ok((subst4, res_ty_subst4))
            }
            Expr::Let(binding, rhs, body) => {
                let (subst1, rhs_ty) = self.infer(env, rhs)?;
                let mut env1 = self.apply_subst_env(&subst1, env);
                let scheme = self.generalize(&env1, &rhs_ty);
                env1.insert(binding.to_string(), scheme.clone());

                let (subst2, body_ty) = self.infer(&env1, &body)?;
                let subst3 = self.compose_subst(&subst2, &subst1);
                Ok((subst3, body_ty))
            }
        }
    }

    fn unify(&self, ty1: &Type, ty2: &Type) -> Result<Subst, InferError> {
        match (ty1, ty2) {
            (Type::TyBool, Type::TyBool) | (Type::TyNat, Type::TyNat) => Ok(Subst::new()),
            (ty, Type::TyVar(name)) | (Type::TyVar(name), ty) => {
                if ty == &Type::TyVar(name.to_string()) {
                    return Ok(Subst::new());
                }
                if self.occurs_check(name, ty) {
                    return Err(InferError::InfiniteType(name.to_string(), ty.clone()));
                }
                let mut subst = Subst::new();
                subst.insert(name.to_string(), (*ty).clone());
                Ok(subst)
            }
            (Type::TyArrow(fun_ty1, arg_ty1), Type::TyArrow(fun_ty2, arg_ty2)) => {
                let subst1 = self.unify(&fun_ty1, &fun_ty2)?;
                let arg_ty1_1 = self.apply_subst(&subst1, &arg_ty1);
                let arg_ty2_1 = self.apply_subst(&subst1, &arg_ty2);
                let subst2 = self.unify(&arg_ty1_1, &arg_ty2_1)?;
                Ok(self.compose_subst(&subst2, &subst1))
            }
            (Type::TyPair(fst_ty1, snd_ty1), Type::TyPair(fst_ty2, snd_ty2)) => {
                let subst1 = self.unify(&fst_ty1, &fst_ty2)?;
                let snd_ty1_1 = self.apply_subst(&subst1, &snd_ty1);
                let snd_ty2_1 = self.apply_subst(&subst1, &snd_ty2);
                let subst2 = self.unify(&snd_ty1_1, &snd_ty2_1)?;
                Ok(self.compose_subst(&subst2, &subst1))
            }
            _ => Err(InferError::UnificationFail((*ty1).clone(), (*ty2).clone())),
        }
    }

    fn instantiate(&mut self, scheme: &TypeScheme) -> Type {
        let mut subst = Subst::new();
        for var in scheme.vars.iter() {
            subst.insert(var.to_string(), self.fresh_type_var());
        }
        self.apply_subst(&subst, &scheme.ty)
    }

    fn apply_subst(&self, subst: &Subst, ty: &Type) -> Type {
        match ty {
            Type::TyBool => Type::TyBool,
            Type::TyNat => Type::TyNat,
            Type::TyArrow(arg_ty, ret_ty) => {
                let arg_ty1 = self.apply_subst(subst, arg_ty);
                let ret_ty1 = self.apply_subst(subst, ret_ty);
                Type::TyArrow(Box::new(arg_ty1), Box::new(ret_ty1))
            }
            Type::TyPair(fst_ty, snd_ty) => {
                let fst_ty1 = self.apply_subst(subst, fst_ty);
                let snd_ty1 = self.apply_subst(subst, snd_ty);
                Type::TyPair(Box::new(fst_ty1), Box::new(snd_ty1))
            }
            Type::TyVar(name) => match subst.get(name) {
                Some(ty1) => (*ty1).clone(),
                None => (*ty).clone(),
            },
        }
    }

    fn apply_subst_env(&self, subst: &Subst, env: &TypeEnv) -> TypeEnv {
        let mut new_env = TypeEnv::new();
        for (name, scheme) in env {
            new_env.insert(name.to_string(), self.apply_subst_scheme(subst, scheme));
        }
        new_env
    }

    // subst1 . subst2
    fn compose_subst(&self, subst1: &Subst, subst2: &Subst) -> Subst {
        let mut subst3 = subst1.clone();
        for (name, ty) in subst2 {
            subst3.insert(name.to_string(), self.apply_subst(subst1, ty));
        }
        subst3
    }

    fn compose_substs(&self, substs: Vec<&Subst>) -> Subst {
        let mut res = Subst::new();
        for subst in substs {
            res = self.compose_subst(subst, &res);
        }
        res
    }

    fn generalize(&self, env: &TypeEnv, ty: &Type) -> TypeScheme {
        let vars_ty = self.free_vars(ty);
        let vars_env = self.free_vars_env(env);
        let mut quantified: Vec<String> = vars_ty.difference(&vars_env).cloned().collect();

        quantified.sort();
        TypeScheme {
            vars: quantified,
            ty: (*ty).clone(),
        }
    }

    fn apply_subst_scheme(&self, subst: &Subst, scheme: &TypeScheme) -> TypeScheme {
        let mut subst1 = subst.clone();
        for var in scheme.vars.iter() {
            subst1.remove(var);
        }
        TypeScheme {
            vars: scheme.vars.clone(),
            ty: self.apply_subst(&subst1, &scheme.ty),
        }
    }

    fn free_vars_env(&self, env: &TypeEnv) -> HashSet<String> {
        let mut res = HashSet::new();
        for (_, scheme) in env {
            res.extend(
                self.free_vars(&scheme.ty)
                    .difference(&HashSet::from_iter(scheme.vars.iter().cloned()))
                    .cloned(),
            );
        }
        res
    }

    fn free_vars(&self, ty: &Type) -> HashSet<String> {
        match ty {
            Type::TyBool => HashSet::new(),
            Type::TyNat => HashSet::new(),
            Type::TyArrow(arg_ty, ret_ty) => {
                let set = self.free_vars(arg_ty);
                set.union(&self.free_vars(ret_ty)).cloned().collect()
            }
            Type::TyPair(fst_ty, snd_ty) => {
                let set = self.free_vars(fst_ty);
                set.union(&self.free_vars(snd_ty)).cloned().collect()
            }
            Type::TyVar(name) => {
                let mut set = HashSet::new();
                set.insert(name.to_string());
                set
            }
        }
    }

    fn occurs_check(&self, var: &str, ty: &Type) -> bool {
        match ty {
            Type::TyVar(name) => name == var,
            Type::TyArrow(t1, t2) => self.occurs_check(var, t1) || self.occurs_check(var, t2),
            Type::TyPair(t1, t2) => self.occurs_check(var, t1) || self.occurs_check(var, t2),
            Type::TyNat | Type::TyBool => false,
        }
    }
}
