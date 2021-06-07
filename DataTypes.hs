module DataTypes where
import Data.Maybe (fromJust)
import Data.List (intersperse)

data Obj = OVar String | ORigid String | OConstr String [Obj] [Mor]
           deriving (Eq)

instance Show Obj where
    show (OVar s) = s
    show (ORigid r) = "'" ++ r
    show (OConstr c os fs) = c ++ "(" ++ show os ++ " , " ++ show fs ++ ")"

data ObjSubst = ObjSubst { vals :: [(String, Obj)] }
                deriving Show

class Substable a where
    applySubst :: ObjSubst -> a -> a

emptyObjSubst :: ObjSubst
emptyObjSubst = ObjSubst []

applyObjSubst :: ObjSubst -> Obj -> Obj
applyObjSubst s (OVar n) = fromJust $ lookup n (vals s)
applyObjSubst s (OConstr c os fs) = OConstr c (map (applySubst s) os) (map (applySubst s) fs)
applyObjSubst s (ORigid r) = ORigid r

instance Substable Obj where
    applySubst = applyObjSubst

data Type = Type { dom :: Obj, codom :: Obj }
          deriving Eq

(.->.) :: Obj -> Obj -> Type
a .->. b = Type a b

applyTypeSubst :: ObjSubst -> Type -> Type
applyTypeSubst s (Type d c) = Type (applySubst s d) (applySubst s c)

instance Show Type where
    show (Type d c) = show d ++ " -> " ++ show c

instance Substable Type where
    applySubst = applyTypeSubst

data PreMor = MVar String Type | MConstr String [Mor] Type
           deriving (Eq)

instance Show PreMor where
    show (MVar f _) = f
    show (MConstr c ms _) = c ++ "(" ++ concat (intersperse ", " $ map show ms) ++ ")"

applyPreMorSubst :: ObjSubst -> PreMor -> PreMor
applyPreMorSubst s (MVar n t) = MVar n (applySubst s t)
applyPreMorSubst s (MConstr n ms t) = MConstr n (map (applySubst s) ms) (applySubst s t)

instance Substable PreMor where
    applySubst = applyPreMorSubst

getPreMorType :: PreMor -> Type
getPreMorType (MVar _ t) = t
getPreMorType (MConstr _ _ t) = t

-- Composition is done in the "categorical order", i.e.
-- if f : A -> B and g : B -> C then Mor [f, g] : A -> C
data Mor = Mor [PreMor] Type
         deriving (Eq, Show)

unitMor :: PreMor -> Mor
unitMor f = Mor [f] (getType f)

varMor :: String -> Type -> Mor
varMor s t = unitMor (MVar s t)

constrMor :: String -> [Mor] -> Type -> Mor
constrMor s fs t = unitMor (MConstr s fs t)

applyMorSubst :: ObjSubst -> Mor -> Mor
applyMorSubst s (Mor fs t) = Mor (map (applySubst s) fs) (applySubst s t)

instance Substable Mor where
    applySubst = applyMorSubst

getMorType :: Mor -> Type
getMorType (Mor _ t) = t

compType :: Type -> Type -> Maybe Type
compType t u = if t_codom == u_dom then Just (t_dom .->. u_codom) else Nothing
    where (Type t_dom t_codom) = t
          (Type u_dom u_codom) = u

class HasType a where
    getType :: a -> Type

instance HasType Type where
    getType = id

getDom :: HasType a => a -> Obj
getDom a = dom $ getType a

getCodom :: HasType a => a -> Obj
getCodom a = codom $ getType a

instance HasType PreMor where
    getType = getPreMorType

instance HasType Mor where
    getType = getMorType

addMor :: PreMor -> Mor -> Maybe Mor
addMor f (Mor fs tMor) =
    case compType (getType f) tMor of
      Nothing -> Nothing
      Just t -> Just $ Mor (f:fs) t

mkMor :: [PreMor] -> Maybe Mor
mkMor [] = Nothing
mkMor (f:fs) = (mkMor fs) >>= addMor f

-- A category is just a set of object constructors and morphisms (which may be polymorphic)
data Cat = Cat { objects :: [Obj], morphisms :: [Mor] }

idMor :: Obj -> Mor
idMor o = constrMor "id" [] (o .->. o)

prod :: Obj -> Obj -> Obj
prod a b = OConstr "prod" [a, b] []

(.*.) :: Obj -> Obj -> Obj
a .*. b = prod a b

pi1 :: Mor
pi1 = constrMor "pi1" [] (a .*. b .->. a)
      where a = OVar "a"
            b = OVar "b"

pi2 :: Mor
pi2 = constrMor "pi2" [] (a .*. b .->. b)
      where a = OVar "a"
            b = OVar "b"

prodMor :: Mor
prodMor = constrMor "prod" [varMor "f" (c .->. a), varMor "g" (c .->. b)] (c .->. (a .*. b))
    where a = OVar "a"
          b = OVar "b"
          c = OVar "c"

pullBack :: Mor -> Mor -> Maybe Obj
pullBack f g = if getCodom f == getCodom g
               then
                 Just $ OConstr "pullBack" [] [f, g]
               else
                 Nothing

pullBacks :: Obj
pullBacks = fromJust $ pullBack f g
    where a = OVar "a"
          b = OVar "b"
          c = OVar "c"
          f = varMor "f" (a .->. b)
          g = varMor "g" (c .->. b)

pbProj1 :: Mor
pbProj1 = unitMor $ MConstr "pbProj1" [] (pbFG .->. a)
    where a = OVar "a"
          b = OVar "b"
          c = OVar "c"
          f = varMor "f" (a .->. b)
          g = varMor "g" (c .->. b)
          pbFG = fromJust $ pullBack f g

pbProj2 :: Mor
pbProj2 = unitMor $ MConstr "pbProj1" [] (pbFG .->. b)
    where a = OVar "a"
          b = OVar "b"
          c = OVar "c"
          f = varMor "f" (a .->. b)
          g = varMor "g" (c .->. b)
          pbFG = fromJust $ pullBack f g


pbInit :: Mor
pbInit = unitMor $ MConstr "pbInit" [h1, h2] (d .->. pbFG)
    where a = OVar "a"
          b = OVar "b"
          c = OVar "c"
          d = OVar "d"
          f = varMor "f" (a .->. b)
          g = varMor "g" (c .->. b)
          h1 = varMor "h1" (d .->. a)
          h2 = varMor "h2" (d .->. c)
          pbFG = fromJust $ pullBack f g


expObj :: Obj -> Obj -> Obj
expObj a b = OConstr "exp" [a, b] []

(.=>.) :: Obj -> Obj -> Obj
a .=>. b = expObj a b

curryMor :: Mor
curryMor = constrMor "curry" [varMor "f" ((a .*. b) .->. c)] (a .->. (b .=>. c))
    where a = OVar "a"
          b = OVar "b"
          c = OVar "c"

eval :: Mor
eval = constrMor "eval" [] (a .*. (a .=>. b) .->. b)
    where a = OVar "a"
          b = OVar "b"
