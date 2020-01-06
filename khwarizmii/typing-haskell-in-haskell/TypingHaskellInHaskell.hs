{-# OPTIONS -Wall #-}
module TypingHaskellInHaskell where

import Data.List (nub, (\\), intersect, union, partition)
import Control.Monad (msum, ap, liftM)

type Id  = String

enumId  :: Int -> Id
enumId n = "v" ++ show n

-- infixr 6 :->:
-- TODO: can't represent (forall x. x)
data Kind  = Star | Kfun Kind Kind | UninhabitedOrImpredicative
             deriving Eq

data Type  = TVar Tyvar | TCon Tycon | TAp  Type Type | TGen Int
             deriving Eq

data Tyvar = Tyvar Id Kind
             deriving Eq

data Tycon = Tycon Id Kind
             deriving Eq

tUnit, tChar, tInt, tInteger, tFloat, tDouble, tList, tArrow, tTuple2 :: Type
tUnit    = TCon (Tycon "()" Star)
tChar    = TCon (Tycon "Char" Star)
tInt     = TCon (Tycon "Int" Star)
tInteger = TCon (Tycon "Integer" Star)
tFloat   = TCon (Tycon "Float" Star)
tDouble  = TCon (Tycon "Double" Star)

tList    = TCon (Tycon "[]" (Kfun Star Star))
tArrow   = TCon (Tycon "(->)" (Kfun Star (Kfun Star Star)))
tTuple2  = TCon (Tycon "(,)" (Kfun Star (Kfun Star Star)))

-- TAp (TAp tArrow tInt) (TAp tList (TVar (Tyvar "a" Star)))

tString    :: Type
tString     = list tChar

infixr      4 `fn`
fn         :: Type -> Type -> Type
a `fn` b    = TAp (TAp tArrow a) b

list       :: Type -> Type
list t      = TAp tList t

pair       :: Type -> Type -> Type
pair a b    = TAp (TAp tTuple2 a) b

class HasKind t where
  kind :: t -> Kind
instance HasKind Tyvar where
  kind (Tyvar _v k) = k
instance HasKind Tycon where
  kind (Tycon _v k) = k
instance HasKind Type where
  kind (TCon tc) = kind tc
  kind (TVar u)  = kind u
  kind (TAp t _) = case (kind t) of
                     (Kfun _ k) -> k
                     k -> k
  kind (TGen _)  = UninhabitedOrImpredicative

type Subst  = [(Tyvar, Type)]

nullSubst  :: Subst
nullSubst   = []

(+->)      :: Tyvar -> Type -> Subst
u +-> t     = [(u, t)]

class Types t where
  apply :: Subst -> t -> t
  tv    :: t -> [Tyvar]

instance Types Type where
  apply s (TVar u)  = case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply _s t        = t

  tv (TVar u)  = [u]
  tv (TAp l r) = tv l `union` tv r
  tv _t        = []

instance Types a => Types [a] where
  apply s = map (apply s)
  tv      = nub . concat . map tv

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

merge      :: Monad m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return (s1++s2) else fail "merge fails"
 where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v))
                   (map fst s1 `intersect` map fst s2)

mgu     :: Monad m => Type -> Type -> m Subst
varBind :: Monad m => Tyvar -> Type -> m Subst

mgu (TAp l r) (TAp l' r') = do s1 <- mgu l l'
                               s2 <- mgu (apply s1 r) (apply s1 r')
                               return (s2 @@ s1)
mgu (TVar u) t        = varBind u t
mgu t (TVar u)        = varBind u t
mgu (TCon tc1) (TCon tc2)
           | tc1==tc2 = return nullSubst
mgu _t1 _t2           = fail "types do not unify"

varBind u t | t == TVar u      = return nullSubst
            | u `elem` tv t    = fail "occurs check fails"
            | kind u /= kind t = fail "kinds do not match"
            | otherwise        = return (u +-> t)

match :: Monad m => Type -> Type -> m Subst

match (TAp l r) (TAp l' r') = do sl <- match l l'
                                 sr <- match r r'
                                 merge sl sr
match (TVar u)   t | kind u == kind t = return (u +-> t)
match (TCon tc1) (TCon tc2)
         | tc1==tc2         = return nullSubst
match _t1 _t2               = fail "types do not match"

data Qual t = [Pred] :=> t
              deriving Eq

data Pred   = IsIn Id Type
              deriving Eq

-- [IsIn "Num" (TVar (Tyvar "a" Star))] :=> (TVar (Tyvar "a" Star) `fn` tInt)

instance Types t => Types (Qual t) where
  apply s (ps :=> t) = apply s ps :=> apply s t
  tv (ps :=> t)      = tv ps `union` tv t

instance Types Pred where
  apply s (IsIn i t) = IsIn i (apply s t)
  tv (IsIn _i t)     = tv t

mguPred, matchPred :: Pred -> Pred -> Maybe Subst
mguPred             = lift mgu
matchPred           = lift match

lift :: Monad m => (Type -> Type -> m a) -> Pred -> Pred -> m a
lift m (IsIn i t) (IsIn i' t')
         | i == i'   = m t t'
         | otherwise = fail "classes differ"

type Class    = ([Id], [Inst])
type Inst     = Qual Pred

-- (["Eq"], [[] :=> IsIn "Ord" tUnit,
--           [] :=> IsIn "Ord" tChar,
--           [] :=> IsIn "Ord" tInt,
--           [IsIn "Ord" (TVar (Tyvar "a" Star)),
--            IsIn "Ord" (TVar (Tyvar "b" Star))]
--              :=> IsIn "Ord" (pair (TVar (Tyvar "a" Star))
--                                   (TVar (Tyvar "b" Star)))])

data ClassEnv = ClassEnv { classes  :: Id -> Maybe Class,
                           defaults :: [Type] }

super     :: ClassEnv -> Id -> [Id]
super ce i = case classes ce i of
              Just (is, _its) -> is
              Nothing -> []

insts     :: ClassEnv -> Id -> [Inst]
insts ce i = case classes ce i of
              Just (_is, its) -> its
              Nothing -> []

defined :: Maybe a -> Bool
defined (Just _x) = True
defined Nothing  = False

modify       :: ClassEnv -> Id -> Class -> ClassEnv
modify ce i c = ce{classes = \j -> if i==j then Just c
                                           else classes ce j}

initialEnv :: ClassEnv
initialEnv  = ClassEnv { classes  = \_i -> fail "class not defined",
                         defaults = [tInteger, tDouble] }

type EnvTransformer = ClassEnv -> Maybe ClassEnv

infixr 5 <:>
(<:>)       :: EnvTransformer -> EnvTransformer -> EnvTransformer
(f <:> g) ce = do ce' <- f ce
                  g ce'

addClass                              :: Id -> [Id] -> EnvTransformer
addClass i is ce
 | defined (classes ce i)              = fail "class already defined"
 | any (not . defined . classes ce) is = fail "superclass not defined"
 | otherwise                           = return (modify ce i (is, []))

addPreludeClasses :: EnvTransformer
addPreludeClasses  = addCoreClasses <:> addNumClasses

addCoreClasses ::   EnvTransformer
addCoreClasses  =   addClass "Eq" []
                <:> addClass "Ord" ["Eq"]
                <:> addClass "Show" []
                <:> addClass "Read" []
                <:> addClass "Bounded" []
                <:> addClass "Enum" []
                <:> addClass "Functor" []
                <:> addClass "Monad" []

addNumClasses  ::   EnvTransformer
addNumClasses   =   addClass "Num" ["Eq", "Show"]
                <:> addClass "Real" ["Num", "Ord"]
                <:> addClass "Fractional" ["Num"]
                <:> addClass "Integral" ["Real", "Enum"]
                <:> addClass "RealFrac" ["Real", "Fractional"]
                <:> addClass "Floating" ["Fractional"]
                <:> addClass "RealFloat" ["RealFrac", "Floating"]

addInst                        :: [Pred] -> Pred -> EnvTransformer
addInst ps p@(IsIn i _) ce
 | not (defined (classes ce i)) = fail "no class for instance"
 | any (overlap p) qs           = fail "overlapping instance"
 | otherwise                    = return (modify ce i c)
   where its = insts ce i
         qs  = [ q | (_ :=> q) <- its ]
         c   = (super ce i, (ps:=>p) : its)

overlap       :: Pred -> Pred -> Bool
overlap p q    = defined (mguPred p q)

exampleInsts ::  EnvTransformer
exampleInsts =   addPreludeClasses
             <:> addInst [] (IsIn "Ord" tUnit)
             <:> addInst [] (IsIn "Ord" tChar)
             <:> addInst [] (IsIn "Ord" tInt)
             <:> addInst [IsIn "Ord" (TVar (Tyvar "a" Star)),
                          IsIn "Ord" (TVar (Tyvar "b" Star))]
                         (IsIn "Ord" (pair (TVar (Tyvar "a" Star))
                                           (TVar (Tyvar "b" Star))))

bySuper :: ClassEnv -> Pred -> [Pred]
bySuper ce p@(IsIn i t)
 = p : concat [ bySuper ce (IsIn i' t) | i' <- super ce i ]

byInst                   :: ClassEnv -> Pred -> Maybe [Pred]
byInst ce p@(IsIn i _t)   = msum [ tryInst it | it <- insts ce i ]
 where tryInst (ps :=> h) = do u <- matchPred h p
                               Just (map (apply u) ps)

entail        :: ClassEnv -> [Pred] -> Pred -> Bool
entail ce ps p = any (p `elem`) (map (bySuper ce) ps) ||
                 case byInst ce p of
                   Nothing -> False
                   Just qs -> all (entail ce ps) qs

inHnf       :: Pred -> Bool
inHnf (IsIn _c t) = hnf t
 where hnf (TVar _v)   = True
       hnf (TCon _tc)  = False
       hnf (TGen _i)   = False
       hnf (TAp t' _)  = hnf t'

toHnfs      :: Monad m => ClassEnv -> [Pred] -> m [Pred]
toHnfs ce ps = do pss <- mapM (toHnf ce) ps
                  return (concat pss)

toHnf                 :: Monad m => ClassEnv -> Pred -> m [Pred]
toHnf ce p | inHnf p   = return [p]
           | otherwise = case byInst ce p of
                           Nothing -> fail "context reduction"
                           Just ps -> toHnfs ce ps

simplify   :: ClassEnv -> [Pred] -> [Pred]
simplify ce = loop []
 where loop rs []                            = rs
       loop rs (p:ps) | entail ce (rs++ps) p = loop rs ps
                      | otherwise            = loop (p:rs) ps

reduce      :: Monad m => ClassEnv -> [Pred] -> m [Pred]
reduce ce ps = do qs <- toHnfs ce ps
                  return (simplify ce qs)

scEntail        :: ClassEnv -> [Pred] -> Pred -> Bool
scEntail ce ps p = any (p `elem`) (map (bySuper ce) ps)

data Scheme = Forall [Kind] (Qual Type)
              deriving Eq

instance Types Scheme where
  apply s (Forall ks qt) = Forall ks (apply s qt)
  tv (Forall _ks qt)     = tv qt

quantify      :: [Tyvar] -> Qual Type -> Scheme
quantify vs qt = Forall ks (apply s qt)
 where vs' = [ v | v <- tv qt, v `elem` vs ]
       ks  = map kind vs'
       s   = zip vs' (map TGen [0..])

toScheme      :: Type -> Scheme
toScheme t     = Forall [] ([] :=> t)

data Assump = Id :>: Scheme

instance Types Assump where
  apply s (i :>: sc) = i :>: (apply s sc)
  tv (_i :>: sc)     = tv sc

find                 :: Monad m => Id -> [Assump] -> m Scheme
find i []             = fail ("unbound identifier: " ++ i)
find i ((i':>:sc):as) = if i==i' then return sc else find i as

newtype TI a = TI (Subst -> Int -> (Subst, Int, a))

instance Monad TI where
  return x   = TI (\s n -> (s,n,x))
  TI f >>= g = TI (\s n -> case f s n of
                            (s',m,x) -> let TI gx = g x
                                        in  gx s' m)

instance Applicative TI where
  pure = return
  (<*>) = ap

instance Functor TI where
  fmap = liftM

runTI       :: TI a -> a
runTI (TI f) = x where (_s,_n,x) = f nullSubst 0

getSubst   :: TI Subst
getSubst    = TI (\s n -> (s,n,s))

unify      :: Type -> Type -> TI ()
unify t1 t2 = do s <- getSubst
                 u <- mgu (apply s t1) (apply s t2)
                 extSubst u

extSubst   :: Subst -> TI ()
extSubst s' = TI (\s n -> (s'@@s, n, ()))

newTVar    :: Kind -> TI Type
newTVar k   = TI (\s n -> let v = Tyvar (enumId n) k
                          in  (s, n+1, TVar v))

freshInst               :: Scheme -> TI (Qual Type)
freshInst (Forall ks qt) = do ts <- mapM newTVar ks
                              return (inst ts qt)

class Instantiate t where
  inst  :: [Type] -> t -> t
instance Instantiate Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen n)  = ts !! n
  inst _ts t        = t
instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
instance Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t
instance Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)

type Infer e t = ClassEnv -> [Assump] -> e -> TI ([Pred], t)

data Literal = LitInt  Integer
             | LitChar Char
             | LitRat  Rational
             | LitStr  String

tiLit            :: Literal -> TI ([Pred],Type)
tiLit (LitChar _) = return ([], tChar)
tiLit (LitInt _)  = do v <- newTVar Star
                       return ([IsIn "Num" v], v)
tiLit (LitStr _)  = return ([], tString)
tiLit (LitRat _)  = do v <- newTVar Star
                       return ([IsIn "Fractional" v], v)

data Pat        = PVar Id
                | PWildcard
                | PAs  Id Pat
                | PLit Literal
                | PNpk Id Integer
                | PCon Assump [Pat]

tiPat :: Pat -> TI ([Pred], [Assump], Type)

tiPat (PVar i) = do v <- newTVar Star
                    return ([], [i :>: toScheme v], v)

tiPat PWildcard   = do v <- newTVar Star
                       return ([], [], v)

tiPat (PAs i pat) = do (ps, as, t) <- tiPat pat
                       return (ps, (i:>:toScheme t):as, t)

tiPat (PLit l) = do (ps, t) <- tiLit l
                    return (ps, [], t)

tiPat (PNpk i _k)  = do t <- newTVar Star
                        return ([IsIn "Integral" t], [i:>:toScheme t], t)

tiPat (PCon (_i:>:sc) pats) = do (ps,as,ts) <- tiPats pats
                                 t'         <- newTVar Star
                                 (qs :=> t) <- freshInst sc
                                 unify t (foldr fn t' ts)
                                 return (ps++qs, as, t')

tiPats     :: [Pat] -> TI ([Pred], [Assump], [Type])
tiPats pats = do psasts <- mapM tiPat pats
                 let ps = concat [ ps' | (ps',_,_) <- psasts ]
                     as = concat [ as' | (_,as',_) <- psasts ]
                     ts = [ t | (_,_,t) <- psasts ]
                 return (ps, as, ts)

data Expr = Var   Id
          | Lit   Literal
          | Const Assump
          | Ap    Expr Expr
          | Let   BindGroup Expr

tiExpr                          :: Infer Expr Type
tiExpr _ce as (Var i)            = do sc         <- find i as
                                      (ps :=> t) <- freshInst sc
                                      return (ps, t)
tiExpr _ce _as (Const (_i:>:sc)) = do (ps :=> t) <- freshInst sc
                                      return (ps, t)
tiExpr _ce _as (Lit l)           = do (ps,t) <- tiLit l
                                      return (ps, t)
tiExpr ce as (Ap e f)            = do (ps,te) <- tiExpr ce as e
                                      (qs,tf) <- tiExpr ce as f
                                      t       <- newTVar Star
                                      unify (tf `fn` t) te
                                      return (ps ++ qs, t)
tiExpr ce as (Let bg e)          = do (ps, as') <- tiBindGroup ce as bg
                                      (qs, t)   <- tiExpr ce (as' ++ as) e
                                      return (ps ++ qs, t)

type Alt = ([Pat], Expr)

tiAlt                :: Infer Alt Type
tiAlt ce as (pats, e) = do (ps, as', ts) <- tiPats pats
                           (qs,t)  <- tiExpr ce (as'++as) e
                           return (ps++qs, foldr fn t ts)

tiAlts             :: ClassEnv -> [Assump] -> [Alt] -> Type -> TI [Pred]
tiAlts ce as alts t = do psts <- mapM (tiAlt ce as) alts
                         _ <- mapM (unify t) (map snd psts)
                         return (concat (map fst psts))

split :: Monad m => ClassEnv -> [Tyvar] -> [Tyvar] -> [Pred] -> m ([Pred], [Pred])
split ce fs gs ps = do
  ps' <- reduce ce ps
  let (ds, rs) = partition (all (`elem` fs) . tv) ps'
  rs' <- defaultedPreds ce (fs++gs) rs
  return (ds, rs \\ rs')

-- stringInc x = show (read x + 1)

-- stringInc :: (Read a, Num a) => String -> String

-- stringInc x = show (read x + 1 :: Int)

type Ambiguity       = (Tyvar, [Pred])

ambiguities          :: ClassEnv -> [Tyvar] -> [Pred] -> [Ambiguity]
ambiguities _ce vs ps = [ (v, filter (elem v . tv) ps) | v <- tv ps \\ vs ]

numClasses :: [Id]
numClasses  = ["Num", "Integral", "Floating", "Fractional", "Real", "RealFloat", "RealFrac"]

stdClasses :: [Id]
stdClasses  = ["Eq", "Ord", "Show", "Read", "Bounded", "Enum", "Ix",
               "Functor", "Monad", "MonadPlus"] ++ numClasses

candidates           :: ClassEnv -> Ambiguity -> [Type]
candidates ce (v, qs) = [ t' | let is = [ i | IsIn i _t <- qs ]
                                   ts = [ t | IsIn _i t <- qs ],
                               all ((TVar v)==) ts,
                               any (`elem` numClasses) is,
                               all (`elem` stdClasses) is,
                               t' <- defaults ce,
                               all (entail ce []) [ IsIn i t' | i <- is ] ]

withDefaults :: Monad m => ([Ambiguity] -> [Type] -> a)
                  -> ClassEnv -> [Tyvar] -> [Pred] -> m a
withDefaults f ce vs ps
    | any null tss  = fail "cannot resolve ambiguity"
    | otherwise     = return (f vps (map head tss))
      where vps = ambiguities ce vs ps
            tss = map (candidates ce) vps

defaultedPreds :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m [Pred]
defaultedPreds  = withDefaults (\vps _ts -> concat (map snd vps))

defaultSubst   :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m Subst
defaultSubst    = withDefaults (\vps ts -> zip (map fst vps) ts)

type Expl = (Id, Scheme, [Alt])

tiExpl :: ClassEnv -> [Assump] -> Expl -> TI [Pred]
tiExpl ce as (_i, sc, alts)
        = do (qs :=> t) <- freshInst sc
             ps         <- tiAlts ce as alts t
             s          <- getSubst
             let qs'     = apply s qs
                 t'      = apply s t
                 fs      = tv (apply s as)
                 gs      = tv t' \\ fs
                 sc'     = quantify gs (qs':=>t')
                 ps'     = filter (not . entail ce qs') (apply s ps)
             (ds,rs)    <- split ce fs gs ps'
             if sc /= sc' then
                 fail "signature too general"
               else if not (null rs) then
                 fail "context too weak"
               else
                 return ds

type Impl   = (Id, [Alt])

restricted   :: [Impl] -> Bool
restricted bs = any simple bs
 where simple (_i, alts) = any (null . fst) alts

tiImpls         :: Infer [Impl] [Assump]
tiImpls ce as bs = do ts <- mapM (\_ -> newTVar Star) bs
                      let is    = map fst bs
                          scs   = map toScheme ts
                          as'   = zipWith (:>:) is scs ++ as
                          altss = map snd bs
                      pss <- sequence (zipWith (tiAlts ce as') altss ts)
                      s   <- getSubst
                      let ps'     = apply s (concat pss)
                          ts'     = apply s ts
                          fs      = tv (apply s as)
                          vss     = map tv ts'
                          gs      = foldr1 union vss \\ fs
                      (ds,rs) <- split ce fs (foldr1 intersect vss) ps'
                      if restricted bs then
                          let gs'  = gs \\ tv rs
                              scs' = map (quantify gs' . ([]:=>)) ts'
                          in return (ds++rs, zipWith (:>:) is scs')
                        else
                          let scs' = map (quantify gs . (rs:=>)) ts'
                          in return (ds, zipWith (:>:) is scs')

-- foldr f a (x:xs) = f x (foldr f a xs)
-- foldr f a []     = a
-- and xs           = foldr (&&) True xs

--  (Bool -> Bool -> Bool) -> Bool -> [Bool] -> Bool

-- f   :: Eq a => a -> Bool
-- f x  = (x==x) || g True
-- g y  = (y<=y) || f True

-- g   :: Ord a => a -> Bool

type BindGroup  = ([Expl], [[Impl]])

-- (x,y) = expr

-- nv = expr
-- x  = fst nv
-- y  = snd nv

tiBindGroup :: Infer BindGroup [Assump]
tiBindGroup ce as (es,iss) =
  do let as' = [ v:>:sc | (v, sc, _alts) <- es ]
     (ps, as'') <- tiSeq tiImpls ce (as'++as) iss
     qss        <- mapM (tiExpl ce (as''++as'++as)) es
     return (ps++concat qss, as''++as')

tiSeq                  :: Infer bg [Assump] -> Infer [bg] [Assump]
tiSeq _ti _ce _as []    = return ([],[])
tiSeq ti ce as (bs:bss) = do (ps,as')  <- ti ce as bs
                             (qs,as'') <- tiSeq ti ce (as'++as) bss
                             return (ps++qs, as''++as')

type Program = [BindGroup]

tiProgram :: ClassEnv -> [Assump] -> Program -> [Assump]
tiProgram ce as bgs = runTI $
                      do (ps, as') <- tiSeq tiBindGroup ce as bgs
                         s         <- getSubst
                         rs        <- reduce ce (apply s ps)
                         s'        <- defaultSubst ce [] rs
                         return (apply (s'@@s) as')
