module STLC.Tait

import Data.Maybe
import Data.List.Elem
import Data.List.Quantifiers
import Decidable.Equality
import Quantifiers
import STLC.Ty

%default total

data Term : List Ty -> Ty -> Type where
  I   : Nat -> Term g A
  Var : Elem a g -> Term g a
  Lam : Term (a::g) b -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b

mutual
  data Val : Ty -> Type where
    VI  : Nat -> Val A
    VCl : Env g -> Term (a::g) b -> Val (a~>b)

  Env : List Ty -> Type
  Env = All Val

-- CBV big-step evaluation relation
data Eval : {0 a : Ty} -> Env g -> Term g a -> Val a -> Type where
  EI   :                                                              Eval e (I n)     (VI n)
  EVar :                                                              Eval e (Var el)  (indexAllPub el e)
  ELam :                                                              Eval e (Lam t)   (VCl e t)
  EApp : Eval e f (VCl e0 t0) -> Eval e a va -> Eval (va::e0) t0 v -> Eval e (App f a)  v

ValOk : {0 t : Ty} -> Val t -> Type
ValOk          (VI n)    = ()
ValOk {t=a~>b} (VCl e t) = {v : Val a} -> ValOk v -> (v2 : Val b ** (ValOk v2, Eval (v::e) t v2))

EnvOk : Env g -> Type
EnvOk e = {0 a : Ty} -> (x : Elem a g) -> ValOk (indexAllPub x e)

envExtend : {0 a : Ty} -> {v : Val a} -> ValOk v -> EnvOk e -> EnvOk (v::e)
envExtend vok = \eok => \case
                          Here => vok
                          There el => eok el

TermOk : Term g a -> Type
TermOk t = {e : Env g} -> EnvOk e -> (v : Val a ** (ValOk v, Eval e t v))

normalize : (t : Term g a) -> TermOk t
normalize (I n)       eok = (VI n ** ((), EI))
normalize (Var el)    eok = (indexAllPub el e ** (eok el, EVar))
normalize (Lam t)     eok = (VCl e t ** (\_, vok => normalize t (envExtend vok eok), ELam))   -- TODO a bug? why is the val not implicit?
normalize (App t1 t2) eok = let (VCl e t ** (vok1,ev1)) = normalize t1 eok
                                (v2 ** (vok2,ev2)) = normalize t2 eok
                                (v3 ** (vok3,ev3)) = vok1 vok2
                              in (v3 ** (vok3, EApp ev1 ev2 ev3))

normCl : (t : Term [] a) -> (v : Val a ** Eval [] t v)
normCl t = let (v**(_,ev)) = normalize t (\el => absurd el) in
           (v**ev)