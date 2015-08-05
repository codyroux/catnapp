module Matching where

import Data.Maybe (isJust)
import DataTypes

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
    case objMatchAux psub pat o of
      Nothing -> Nothing
      Just (psub', newCsts) -> objMatchList psub' (newCsts ++ csts)

objMatchAux :: ObjSubst -> Obj -> Obj -> Maybe (ObjSubst, [(Obj, Obj)])
objMatchAux psub (OVar s) t = addSubst s t psub >>= \x -> return (x, [])
objMatchAux psub (ORigid r) (ORigid r') | r == r' = return (psub, [])
objMatchAux psub (OConstr c os _) (OConstr c' os' _) | c == c' = return (psub, zip os os')
objMatchAux psub _ _ = Nothing


tyMatch :: Type -> Type -> Maybe ObjSubst
tyMatch (Type d1 c1) (Type d2 c2) = objMatchInit d1 d2 >>= \s -> objMatch s c1 c2

domMatch :: Type -> Type -> Maybe ObjSubst
domMatch = undefined

codomMatch :: Type -> Type -> Maybe ObjSubst
codomMatch = undefined

-- TODO: Apply the substitution to the morphisms!
exactFind :: [Mor] -> Type -> [Mor]
exactFind ms t = filter (\f -> isJust (tyMatch (getType f) t)) ms

domFind :: [Mor] -> Type -> [Mor]
domFind = undefined

codomFind :: [Mor] -> Type -> [Mor]
codomFind = undefined
