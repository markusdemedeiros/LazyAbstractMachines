{-# LANGUAGE TypeSynonymInstances #-}
module Lib where

import Data.Set (Set)
import qualified Data.Set as S
import Data.List (intersperse, concat, intercalate)
import Data.Char (isDigit)


todo = undefined


-- Normalized lambda expression with variable type a
--  *Normalization*: replace applications to expressions with let bindings
--  Variables in let bindings muse be distinct
--  Application argument must be a variable
data Lambda a
    = Lam { var  :: a,
            expr :: Lambda a }
    | App { exp1 :: Lambda a,
            exp2 :: Lambda a }
    | Var { var  :: a }
    | Let { args :: Set (a, Lambda a)
          , expr :: Lambda a }
    deriving (Show, Eq, Ord)



-- subst E1 E2 x := E1[E2/x]
-- TODO: Will normalized lambda expressions always substitute to normalized lambda expresions?
-- TODO: Clean the Let case up
subst :: (Eq a, Ord a) => Lambda a -> Lambda a -> a -> Lambda a
subst e1@(Var v1) e2 v2 
    | v1 == v2          = e2
    | otherwise         = e1
subst e1@(Lam v1 s1) e2 v2
    | v1 == v2          = e1
    | otherwise         = Lam {var=v1, expr=(subst s1 e2 v2) }
subst e1@(App s1 s2) e2 v2
                        = App {exp1=(subst s1 e2 v2), exp2=(subst s2 e2 v2)}
subst e1@(Let a1 s1) e2 v2
    | (a1 `binds` v2)   = e1
    | otherwise         = Let {args=(S.map (\(vi, ei)->(vi, (subst ei e2 v2))) a1), expr=(subst s1 e2 v2)}
    where binds args1 var1 = S.member var1 $ S.map fst args1


used_vars :: (Eq a, Ord a) => Lambda a -> Set a
used_vars (Lam a e)     = S.union (S.singleton a) (used_vars e)
used_vars (App e1 e2)   = S.union (used_vars e1) (used_vars e2)
used_vars (Var v)       = S.singleton v
used_vars (Let ar ex)   = S.unions [S.unions (S.map (used_vars . snd) ar), S.map fst ar, used_vars ex]


free_vars :: (Eq a, Ord a) => Lambda a -> Set a
free_vars (Lam a e) = S.difference (free_vars e) (S.singleton a)
free_vars (App e1 e2) = S.union (free_vars e1) (free_vars e2)
free_vars (Var v) = S.singleton v
free_vars (Let ar ex) = S.difference (S.union bindings_free expression_free) binds
    where 
        bindings_free = S.unions $ S.map (free_vars . snd) ar
        expression_free = free_vars ex
        binds = S.map fst ar


is_normal :: (Eq a, Ord a) => Lambda a -> Bool
is_normal (Var _)           = True
is_normal (Lam _ e)         = is_normal e
is_normal (App (Lam _ e) 
                (Var _))    = is_normal e
is_normal (Let arg exp)     = (is_normal exp) && S.foldr (\(_, ei) acc -> acc && is_normal ei) True arg





type Envof a b = Set (a, b)

dom :: (Ord a) => (Envof a b) -> Set a
dom = S.map fst 

rng :: (Ord b) => (Envof a b) -> Set b
rng = S.map snd

-- Throws an error if the given enviornment has zero 
env_find :: (Ord a, Show a) => Envof a b -> a -> Either b Int
env_find env a 
    | S.size search == 1 = Left b
    | otherwise = Right (S.size search)
    where 
        search = S.filter ((== a) . fst) $ env
        b = snd . head . S.toList $ search

-- Remove by key/value pair. By set rules, there should only be one. 
env_remove :: (Ord a, Ord b) => a -> b -> Envof a b -> Envof a b
env_remove a b = S.filter (/= (a,b))


env_update :: (Ord a, Ord b) => a -> b -> Envof a b -> Envof a b
env_update a b = S.union (S.singleton (a,b)) . S.filter ((/= a) . fst) 

-- TODO: Normalization script
-- TODO: Syntax equality

-- Mark I machine

type VarI       = String
type ExprI      = Lambda VarI
type HeapI      = Envof VarI ExprI
type StackVarI  = Either VarI VarI  -- Left: p. Right: #p.
type StackI     = [StackVarI]
type MachineI   = (HeapI, ExprI, StackI)

type TraceI     = [StepI]

data StepTI     = App1
                | App2
                | Var1
                | Var2
                | LetS
                | Whnf
                | Done
                deriving (Show, Eq)

type StepI = (StepTI, MachineI)


type VarII      = VarI
type ExprII     = ExprI 
type EnvII      = Envof VarII VarII
type HeapII     = Envof VarII (ExprII, EnvII)
type StackVarII = StackVarI
type StackII    = StackI
type MachineII  = (HeapII, ExprII, EnvII, StackII)
type StepII     = (StepTI, MachineII)
type TraceII    = [StepII]




step_markII :: MachineII -> StepII
step_markII (gamma, App e (Var x), env, s)
    = case env_find env x of 
        (Left p)  -> (App1, (gamma, e, env, (Left p):s))
        (Right n) -> error $ "Enviornment contains " ++ show n ++ " bindings for " ++ x ++ ", expected 1"
step_markII (gamma, (Lam y e), env, (Left p):s)
    = (App2, (gamma, e, env_update y p env, s))
step_markII (gamma, Var x, env, s)
    = case env_find env x of 
        -- No rule applies in this case, though I'm not convinvinced this should ever be reached in closed, normal exprs
        -- Not putting this as an error until I see a proof
        (Right n) -> (Done, (gamma, (Var x), env, s))
        (Left p) -> case env_find gamma p of
            (Right n) -> (Done, (gamma, (Var x), env, s))
            (Left r@(e1, env1)) -> (Var1, ((env_remove p r gamma), e1, env1, (Right p):s))
step_markII (gamma, l@(Lam y e), env, (Right p):s)
    = (Var2, (env_update p (l, env) gamma, l, env, s))
step_markII (gamma, (Let as e), env, s)
    = (LetS, (gamma1, e, env1, s))
    where
        stack_vars  = from_either <$> s
        -- TODO: refactor
        -- heap_vars_1 = S.toList $ dom gamma
        heap_vars
            = S.toList . S.unions $ [ dom gamma
                , S.unions . S.map (used_vars . fst) . rng $ gamma
                , S.unions . S.map (dom . snd) . rng $ gamma
                , S.unions . S.map (rng . snd) . rng $ gamma ]
        expr_vars   = S.toList $ used_vars e

        bindings    = S.toList $ S.map fst as
        fresh_bindings
                    = freshenI (stack_vars ++ heap_vars ++ expr_vars) bindings
        rebind :: VarI -> VarI
        rebind = keyValueMap bindings fresh_bindings "no rebinding found"

        -- WITHOUT TRIMMING
        -- env1 = foldr ((\(stale, fresh) acc_env -> env_update stale fresh acc_env)) env (zip bindings fresh_bindings)
        -- gamma1 = S.union gamma $ S.map (\(x, ei) -> (rebind x, (ei, env1))) as

        -- TRIMMING
        env1_pre = foldr ((\(stale, fresh) acc_env -> env_update stale fresh acc_env)) env (zip bindings fresh_bindings)
        env1 = trim_II e env1_pre
        gamma1 = S.union gamma $ S.map (\(x, ei) -> (rebind x, (ei, (trim_II ei env1_pre)))) as

step_markII m = (Done, m)


-- Trim the enviornment EnvII with the free variables in ExprII
-- Free variables computed at call time instead of being explicitly passed forward 
-- for simplicity
trim_II :: ExprII -> EnvII -> EnvII
trim_II e = S.filter (\bind -> S.member (fst bind) free)
    where free = free_vars e


pprint_markII_step :: StepII -> String
pprint_markII_step (step, (heap, exp, env, stack)) 
    = show step ++ " HEAP\t" ++ (pprint_heapII $ S.toList heap) 
                ++ "\n     CTRL\t" ++ pprint_term exp 
                ++ "\n     ENVR\t" ++ pprint_env env
                ++ "\n     STCK\t" ++ pprint_stack stack 
                ++ "\n" 


pprint_markI_step :: StepI -> String
pprint_markI_step (step, (heap, exp, stack)) 
    = show step ++ " HEAP\t" ++ (pprint_heap $ S.toList heap) ++ "\n     CTRL\t" ++ pprint_term exp ++ "\n     STCK\t" ++ pprint_stack stack ++ "\n" 


pprint_stack :: [StackVarI] -> String
pprint_stack st = "|: " ++ (intercalate " " . (map pretty_elem) . reverse $ st)
    where pretty_elem (Left s) = s
          pretty_elem (Right s) = '#':s

pprint_heap :: [(VarI, ExprI)] -> String
pprint_heap hp = "{" ++ heap_binds ++ "}"
    where heap_binds = intercalate ", " . map pprint_binding $ hp

pprint_heapII :: [(VarII, (ExprII, EnvII))] -> String
pprint_heapII hp = "{" ++ heap_binds ++ "}"
    where heap_binds = intercalate ", " . map pprint_bindingII $ hp


pprint_term :: ExprI -> String
pprint_term (Var v) = v
pprint_term (Lam var exp) = "\955" ++ var ++ ". " ++ pprint_term exp
pprint_term (App ex1 ex2) = "(" ++ pprint_term ex1 ++ ") " ++ pprint_term ex2
pprint_term (Let arg exp) = "let {" ++ pprint_arg ++"} in " ++ (pprint_term exp)
    where pprint_arg = intercalate ", " . S.toList . S.map pprint_binding $ arg


pprint_binding :: (VarI, ExprI) -> String
pprint_binding (sym, bind) = sym ++ " \x21A6 " ++ pprint_term bind


pprint_bindingII :: (VarII, (ExprII, EnvII)) -> String
pprint_bindingII (sym, (e, env)) = sym ++ " \x21A6 (" ++  pprint_term e ++ ", " ++ pprint_env env ++ ")"

pprint_env :: EnvII -> String
pprint_env env = "[" ++ (intercalate ", " . S.toList . S.map pprint_map $ env ) ++ "]"
    where pprint_map (s1, s2) = s1 ++ " \x21A6 " ++ s2

pprint_env_domain :: EnvII -> String
pprint_env_domain _ = "[env]"


pprint_markI :: TraceI -> String
pprint_markI = concat . intersperse "\n" . map pprint_markI_step


pprint_markII :: TraceII -> String
pprint_markII = concat . intersperse "\n" . map pprint_markII_step



step_markI :: MachineI -> StepI
step_markI (gamma, App e (Var p), s)
    = (App1, (gamma, e, (Left p):s)) 
step_markI (gamma, App e _, s) 
    = error "Expression normality was not preserved"
step_markI (gamma, Lam y e, ((Left p):s))
    = (App2, (gamma, subst e (Var p) y, s))
step_markI (gamma, Var p, s)
    | S.size heapsearch == 1 = (Var1, (S.difference gamma heapsearch, e, (Right p):s))
    | otherwise = error $ "Heap contains " 
                            ++ show (length heapsearch) 
                            ++ " bindings for " 
                            ++ p 
                            ++ if (length heapsearch == 0) then " (possible black hole)" else " (compilation error)"
    where 
        heapsearch = S.filter ((== p) . fst) gamma
        e = snd . head . S.toList $ heapsearch
step_markI (gamma, ex@(Lam y e), ((Right p):s))
    = (Var2, (S.union gamma (S.singleton (p, ex)), ex, s))
step_markI (gamma, el@(Let as e), s)
    = (LetS, (gamma1, ehat, s))
    where
        stack_vars  = from_either <$> s
        heap_vars   = S.toList $ dom gamma
        expr_vars   = S.toList $ used_vars el
        
        bindings    = S.toList $ S.map fst as
        fresh_bindings
                    = freshenI (stack_vars ++ heap_vars ++ expr_vars) bindings
        rebind :: VarI -> VarI
        rebind = keyValueMap bindings fresh_bindings "no rebinding found"

        remap :: ExprI -> ExprI
        remap = foldl1 (.) $ zipWith (\stale fresh -> (\ex -> subst ex (Var fresh) stale)) bindings fresh_bindings

        gamma1 = S.union gamma $ S.map (\(x, ei) -> (rebind x, remap ei)) as
        ehat = remap e

step_markI m@(_, Lam _ _, _)
    = (Whnf, m)

keyValueMap :: (Eq a) => [a] -> [b] -> String -> a -> b
keyValueMap [] [] e _           = error e
keyValueMap (a:as) [] e _       = error "KeyValueMap: Insufficient values"
keyValueMap [] (b:bs) e _       = error "KeyValueMap: Insufficient keys"
keyValueMap (a:as) (b:bs) err a1
    | a == a1                   = b
    | otherwise                 = keyValueMap as bs err a1



-- Takes a list of stale variables
-- Returns two functions:
--          Forbidden variables
--                    Variables to create new mutally fresh variables for
--                    No variables will be the same
freshenI :: [VarI] -> [VarI] -> [VarI]
freshenI _ [] = []
freshenI forbidden (b:bs) = b1 : freshenI (b1 : forbidden) bs
    where b1 = gensym forbidden b


-- Friendly gensym: Increments a numeric suffix at the end of a VarI 
-- until it is no longer forbidden
gensym :: [VarI] -> VarI -> VarI
gensym forbidden bias = head . filter (not . flip elem forbidden) . map ((base_prefix ++) . show) $ [numeric_suffix..]
    where
        base_prefix = takeWhile (not . isDigit) $ bias
        -- Return the next numeric suffix of a variable to try
        numeric_suffix 
            = case (reverse . takeWhile isDigit . reverse $ bias) of
                "" -> 0
                n -> 1 + (read n :: Int)



from_either :: Either a a -> a
from_either (Left x) = x
from_either (Right x) = x


-- REQUIRES: e is closed 
-- REQUIRES: e is normal
mark1_stepper :: ExprI -> TraceI
mark1_stepper e = do_step fresh_machine
    where 
        do_step ms 
            = case step_markI ms of 
                s@(Whnf, _) -> [s]
                s@(_, ms1) -> s:(do_step ms1)
        fresh_machine 
            = (S.empty, e, [])


-- REQUIRES: e is closed 
-- REQUIRES: e is normal
mark2_stepper :: ExprII -> TraceII
mark2_stepper e = do_step fresh_machine
    where 
        do_step ms 
            = case step_markII ms of 
                s@(Whnf, _) -> [s]
                s@(Done, _) -> [s]
                s@(_, ms1) -> s:(do_step ms1)
        fresh_machine 
            = (S.empty, e, S.empty, [])



example_figure4 :: ExprI
example_figure4 
    = Let   (S.fromList [ ("y", Lam "x" (Var "x"))
                        , ("v", (App (Lam "z" (Var "z")) (Var "y")))]) 
            (App (Var "v") (Var "v"))

example_2_3 :: ExprI
example_2_3
    = Let   (S.singleton ("s", Lam "z" (Var "z"))) $
            Let (S.fromList     [ ("p", App (Var "q") (Var "s"))
                                , ("q", (Lam "y" (Let (S.singleton ("r", Var "y")) (Var "r"))))])
                (Var "p")

example_capture_test :: ExprI
example_capture_test = Let (S.singleton ("x", Var "x")) (App (Lam "y" (Lam "x" (Var "y"))) (Var "x"))

example_blackhole :: ExprI
example_blackhole = Let (S.singleton ("x", (Var "x"))) (Var "x")

example_spaceleak :: ExprII
example_spaceleak = Let (S.singleton ("f", (Lam "n" (Let (S.singleton ("x", (Lam "y" (Var "y")))) (App (Var "f") (Var "x")) )))) (App (Var "f") (Var "f"))


testI :: ExprI -> IO()
testI s = do
    putStr "Evaluate: "
    putStrLn $ pprint_term s 
    putStr "\n"
    putStrLn . pprint_markI . mark1_stepper $ s

testII :: ExprII -> IO()
testII s = do
    putStr "Evaluate: "
    putStrLn $ pprint_term s 
    putStr "\n"
    putStrLn . pprint_markII . mark2_stepper $ s

testII_diverge :: ExprII -> IO()
testII_diverge s = do
    putStr "Evaluate: "
    putStrLn $ pprint_term s 
    putStr "\n"
    putStrLn . pprint_markII . take 100 . mark2_stepper $ s
    putStrLn "COMPUTATION HALTED AFTER 100 STEPS"
