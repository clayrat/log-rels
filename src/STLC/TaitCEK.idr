module STLC.TaitCEK

import Data.Maybe
import Data.List.Elem
import Data.List.Quantifiers
import Decidable.Equality
import Path
import STLC.Ty

%default total

-- TODO change Data.List.Quantifiers.indexAll to `public export`
indexAllPub : Elem x xs -> All p xs -> p x
indexAllPub  Here     (p::_  ) = p
indexAllPub (There e) ( _::ps) = indexAllPub e ps


data Term : List Ty -> Ty -> Type where
  TT  : Term g A
  Var : Elem a g -> Term g a
  Lam : Term (a::g) b -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b

mutual
  data Val : Ty -> Type where
    VT  : Val A
    VCl : Env g -> Term (a::g) b -> Val (a~>b)

  Env : List Ty -> Type
  Env = All Val

data Closure : Ty -> Type where
  MkClos : Env g -> Term g a -> Closure a

data Frame : Ty -> Ty -> Type where
  CF : Closure s -> Frame (s~>t) t
  CV : Val (s~>t) -> Frame s t

Cont : Ty -> Ty -> Type
Cont = Path Frame

data State : Ty -> Type where
  Exp : Closure a -> Cont a z -> State z
  Con : Val a -> Cont a z -> State z

data Progressing : State z -> Type where
  PExp : {0 c : Closure a} -> {0 k : Cont a z} -> Progressing (Exp c k)
  PCon : {0 v : Val a} -> {0 f : Frame a b} -> {0 k : Cont b z} -> Progressing (Con v (f :: k))

load : Term [] a -> State a
load t = Exp (MkClos [] t) []

doApp : Val (a ~> b) -> Val a -> Cont b z -> State z
doApp (VCl e t) u k = Exp (MkClos (u :: e) t) k

progress : (s : State z) -> Progressing s -> State z
progress (Exp (MkClos e  TT      ) k) PExp = Con VT k
progress (Exp (MkClos e (Var el) ) k) PExp = Con (indexAllPub el e) k
progress (Exp (MkClos e (Lam t)  ) k) PExp = Con (VCl e t) k
progress (Exp (MkClos e (App t u)) k) PExp = Exp (MkClos e t) (CF (MkClos e u) :: k)
progress (Con v (CF c::k))            PCon = Exp c (CV v::k)
progress (Con v (CV u::k))            PCon = doApp u v k

data Step : State a -> State a -> Type where
  It : (sp : Progressing s) -> Step s (progress s sp)

Steps : State a -> State a -> Type
Steps = Path Step

mutual
  -- a closure is good if it always reduces to a good value and this reduction happens under any continuation
  ClosOk : {t : Ty} -> Closure t -> Type
  ClosOk c = (v : Val t ** (ValOk v, {0 z : Ty} -> (k : Cont t z) -> Steps (Exp c k) (Con v k)))

  -- a value is good if
  --   * it's TT
  --   * it's a function which returns a good closure when applied to a good value
  ValOk : Val t -> Type
  ValOk           VT       = ()
  ValOk {t=a~>_} (VCl e t) = (v : Val a) -> ValOk v -> ClosOk (MkClos (v::e) t)

-- an environment is good if all its values are good
EnvOk : Env g -> Type
EnvOk e = {0 a : Ty} -> (el : Elem a g) -> ValOk (indexAllPub el e)

-- a term is good if when combined with any good environment the resulting closure is good
TermOk : Term g a -> Type
TermOk t = {e : Env g} -> EnvOk e -> (v : Val a ** (ValOk v, {0 z : Ty} -> (k : Cont a z) -> Steps (Exp (MkClos e t) k) (Con v k)))

LamOk : {t : Term (a::g) b} -> TermOk t -> TermOk (Lam t)
LamOk tok eok = (VCl e t ** ( \v, vok => tok $ \case
                                                  Here => vok
                                                  There el => eok el
                            , \k => [It PExp] ))

AppOk : {0 t : Term g (a~>b)} -> {u : Term g a} ->
        TermOk t -> TermOk u -> TermOk (App t u)
AppOk tok uok eok = let (VCl et tt ** (vtok, vtst)) = tok eok
                        (vu ** (vuok, vust)) = uok eok
                        (vx ** (vxok, vxst)) = vtok vu vuok
                     in
                    (vx ** (vxok, \k => joinPath (It PExp :: vtst (CF (MkClos e u) :: k)) $  -- focus on t and reduce to a value
                                        joinPath (It PCon :: vust (CV (VCl et tt) :: k)) $   -- focus on u and reduce to a value
                                                 (It PCon :: vxst k)))                       -- reduce the body to value

fundamentalProperty : (t : Term g a) -> TermOk t
fundamentalProperty  TT       = \eok => (VT ** ((), \k => [It PExp]))
fundamentalProperty (Var el)  = \eok => (indexAllPub el e ** (eok el, \k => [It PExp]))
fundamentalProperty (Lam t)   = LamOk $ fundamentalProperty t
fundamentalProperty (App t u) = AppOk (fundamentalProperty t) (fundamentalProperty u)

terminate : (t : Term [] a) -> (v : Val a ** Steps (load t) (Con v []))
terminate t = let (v ** (_, vst)) = fundamentalProperty t $ \el => absurd el in
              (v ** vst [])
