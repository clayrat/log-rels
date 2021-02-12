module STLC.Tait

import Data.Maybe
import Decidable.Equality
import STLC.Ty

%default total

public export
data Term0 = I0 Nat
           | Var0 String
           | Lam0 String Term0
           | App0 Term0 Term0

data Env a = Nil | Cons (Env a) String a

lookupEnv : Env a -> String -> Maybe a
lookupEnv Nil _ = Nothing
lookupEnv (Cons e y a) x with (decEq x y)
  lookupEnv (Cons e y a) x | Yes eq = Just a
  lookupEnv (Cons e y a) x | No _   = lookupEnv e x

TEnv : Type
TEnv = Env Ty

data Term : TEnv -> Term0 -> Ty -> Type where
  I   : {n : Nat}                     -> Term g (I0 n)       A
  Var : {x : String} ->
        lookupEnv g x = Just a        -> Term g (Var0 x)     a
  Lam : {x : String} -> {t0 : Term0} ->
        {a : Ty} ->
        Term (Cons g x a) t0 b         -> Term g (Lam0 x t0) (a~>b)
  App : Term g f (a~>b) -> Term g x a -> Term g (App0 f x)   b

mutual
  data Val = VI Nat | VCl DEnv String Term0

  DEnv : Type
  DEnv = Env Val

data Eval : DEnv -> Term0 -> Val -> Type where
  EI   :                            Eval e (I0 n)     (VI n)
  EVar : lookupEnv e x = Just v ->  Eval e (Var0 x)    v
  ELam :                            Eval e (Lam0 x t) (VCl e x t)
  EApp : Eval e f (VCl e0 x t0) ->
         Eval e a va ->
         Eval (Cons e x va) t0 v -> Eval e (App0 f a)  v

-- the logical relation
Equiv : Val -> Ty -> Type
Equiv v  A        = (n : Nat ** v = VI n)
Equiv v (Imp a b) = (x : String ** t : Term0 ** e : DEnv **
                     ( v = VCl e x t
                     , {v1 : Val} ->
                       Equiv v1 a ->
                       (v2 : Val ** (Eval (Cons e x v1) t v2, Equiv v2 b))
                     )
                    )

EquivEnv : DEnv -> TEnv -> Type
EquivEnv e g = {x : String} ->
               ( {0 v1 : Val} ->
                 lookupEnv e x = Just v1 -> (ty1 : Ty ** (lookupEnv g x = Just ty1, Equiv v1 ty1))
               , {0 ty1 : Ty} ->
                 lookupEnv g x = Just ty1 -> (v1 : Val ** (lookupEnv e x = Just v1, Equiv v1 ty1))
               )

Look : {s : String} -> EquivEnv e g -> lookupEnv g s = Just ty -> (v : Val ** (lookupEnv e s = Just v, Equiv v ty))
Look ee = snd ee

EquivExtend : {s : String} -> {v : Val} -> {ty : Ty} ->
              Equiv v ty -> EquivEnv e g -> EquivEnv (Cons e s v) (Cons g s ty)
EquivExtend eq ee with (decEq x s)
  EquivExtend eq ee | Yes prf = ( \e1 => (ty ** (Refl, rewrite sym $ justInjective e1 in eq))
                                , \e2 => (v ** (Refl, rewrite sym $ justInjective e2 in eq))
                                )
  EquivExtend eq ee | No ctra = ee

Normalisation : {e : DEnv} ->
                Term g t1 ty -> EquivEnv e g -> (v : Val ** (Eval e t1 v, Equiv v ty))
Normalisation (I {n})          ee = (VI n ** (EI, (n ** Refl)))
Normalisation (Var prf)        ee = let (v**(prf1,eq)) = Look ee prf in
                                    (v ** (EVar prf1, eq))
Normalisation (Lam {x} {t0} t) ee = (VCl e x t0 ** (ELam, (x ** t0 ** e ** (Refl, \eq => Normalisation t (EquivExtend eq ee)))))
Normalisation (App t1 t2)      ee = ?wat