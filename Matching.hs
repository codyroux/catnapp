module Matching where

import Control.Monad.Free (join, liftM2)
import Data.Maybe (isJust, catMaybes)
import DataTypes

-- We correctly handle non-linearity
addSubst :: String -> Obj -> ObjSubst -> Maybe ObjSubst
addSubst s o (ObjSubst subs) =
    case lookup s subs of
      Nothing -> Just $ ObjSubst $ (s, o):subs
      Just o' -> if o == o' then Just (ObjSubst subs)
                else Nothing

-- Match an object "pattern" against a concrete object
objMatch :: ObjSubst -> Obj -> Obj -> Maybe ObjSubst
objMatch subs pat obj = objMatchList subs [(pat, obj)]

objMatchInit :: Obj -> Obj -> Maybe ObjSubst
objMatchInit = objMatch (ObjSubst [])

objMatchList :: ObjSubst -> [(Obj, Obj)] -> Maybe ObjSubst
objMatchList psub [] = Just psub
objMatchList psub ((pat, o):csts) =
  do
    (psub', newCsts) <- objMatchAux psub pat o
    objMatchList psub' (newCsts ++ csts)

objMatchAux :: ObjSubst -> Obj -> Obj -> Maybe (ObjSubst, [(Obj, Obj)])
objMatchAux psub (OVar s) t = addSubst s t psub >>= \x -> return (x, [])
objMatchAux psub (ORigid r) (ORigid r') | r == r' = return (psub, [])
-- Don't try to match on morphisms for now?
objMatchAux psub (OConstr c os _) (OConstr c' os' _) | c == c' = return (psub, zip os os')
objMatchAux psub _ _ = Nothing

compSubst :: ObjSubst -> ObjSubst -> Maybe ObjSubst
compSubst o1 o2 = addAll (vals o1) o2
  where addAll [] o = Just o
        addAll ((v, t):vs) o = (addAll vs o) >>= addSubst v t

tyMatch :: Type -> Type -> Maybe ObjSubst
tyMatch (Type d1 c1) (Type d2 c2) = objMatchInit d1 d2 >>= \s -> objMatch s c1 c2

tyMatchList :: ObjSubst -> [(Type, Type)] -> Maybe ObjSubst
tyMatchList s [] = Just s
tyMatchList s ((pat, ty):ps) =
  do
    s' <- tyMatch pat ty
    compSubst s' s

domMatch :: Type -> Type -> Maybe ObjSubst
domMatch (Type d1 _) (Type d2 _) = objMatchInit d1 d2

codomMatch :: Type -> Type -> Maybe ObjSubst
codomMatch (Type _ c1) (Type _ c2) = objMatchInit c1 c2

-- This is a very stupid algorithm, since it can fail because we
-- picked stupid objects.  It might be worth asking that object
-- constructors have no "redundant" data, e.g. objects that are just
-- domains or codomains of some defining morphisms
findObjAux :: Obj -> [Obj] -> [Mor] -> Maybe ObjSubst
findObjAux (OConstr _ oPat morPat) objs mors =
  join $ liftM2 compSubst morSubst objSubst
  where morSubst =
          tyMatchList emptyObjSubst $ zip (map getMorType morPat) (map getMorType mors)
        objSubst =
          objMatchList emptyObjSubst $ zip oPat objs
-- TODO: handle rigid case
findObjAux _ _ _ = Nothing


findObj :: Obj -> [Obj] -> [Mor] -> Maybe Obj
findObj o os ms =
  do
    sub <- findObjAux o os ms
    return $ applySubst sub o

findObjs :: Obj -> [Obj] -> [Mor] -> [Obj]
findObjs o os ms = catMaybes [findObj o os ms]

test :: Maybe ObjSubst
test = findObjAux pullBacks [] [h, i]
  where u = ORigid "u"
        v = ORigid "v"
        w = ORigid "w"
        h = rigidMor "h" (u .->. v)
        i = rigidMor "i" (w .->. v)
