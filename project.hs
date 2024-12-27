-- Helper Functions
-- Allowed variable names - List of all possible Haskell characters
allVariables = ['a' .. ]

-- Find a fresh variable that is not in use
freshVariable usedVars = head (filter (`notElem` usedVars) allVariables)

-- Function to gather free variables in a term
freeVars (Var x) = [x]
freeVars (Abs x t) = filter (/= x) (freeVars t)
freeVars (App t1 t2) = freeVars t1 ++ freeVars t2
-------------------------------------------------------------------------

-- Q1)
data Term = Var Char            -- Variable
            | Abs Char Term     -- Abstraction, λx. t
            | App Term Term     -- Application, (t1 t2)
    deriving Eq
-------------------------------------------------------------------------

-- Q2)
-- (a) (λc.cc)
termA = Abs 'c' (App (Var 'c') (Var 'c'))

-- (b) (λc.cd)
termB = Abs 'c' (App (Var 'c') (Var 'd'))

-- (c) (λx.xy)(λy.xy)
termC = App (Abs 'x' (App (Var 'x') (Var 'y'))) (Abs 'y' (App (Var 'x') (Var 'y')))

-- (d) (λy.x)y
termD = App (Abs 'y' (Var 'x')) (Var 'y')

-- (e) (λy.x)a
termE = App (Abs 'y' (Var 'x')) (Var 'a')
-------------------------------------------------------------------------

-- Q3)
instance Show Term where
    show (Var x) = [x]
    show (Abs x t) = "(λ" ++ [x] ++ "." ++ show t ++ ")"
    show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
-------------------------------------------------------------------------

-- Q4)
substitute (Var x) var replacement
    | (x == var) = replacement
    | otherwise = (Var x)
substitute (Abs x t) var replacement
    | (x == var) = (Abs x t)  -- No substitution if the bound variable `x` has to be substituted
    | x `elem` (freeVars replacement) = substitute (Abs fresh (substitute t x (Var fresh))) var replacement
    -- If `x` is a free variable in `replacement`, we replace all occurences of `x` in `t` by an unused variable
    -- and then perform substitution
    | otherwise = Abs x (substitute t var replacement)
    where fresh = freshVariable (freeVars t ++ freeVars replacement ++ [var])
    -- `fresh` returns an unused variable
substitute (App t1 t2) var replacement = 
    App (substitute t1 var replacement) (substitute t2 var replacement)
-------------------------------------------------------------------------

--Q5)
-- This also does alpha renaming where necessary because the `substitute` function takes care of it
betaReduce (App (Abs x t1) t2) = betaReduce (substitute t1 x t2)
betaReduce (App t1 t2) = App (betaReduce t1) (betaReduce t2)
betaReduce (Abs x t) = Abs x (betaReduce t)
betaReduce t = t  -- Variables remain unchanged
-------------------------------------------------------------------------

-- Q6)
-- Function to alpha reduce or convert a λ term's bound variable `old` to `new`
alphaReduce (Var x) old new
    | (x == old) = (Var new)
    | otherwise = (Var x)
alphaReduce (Abs x t) old new
    | (x == old) = Abs new (alphaReduce t old new)
    | otherwise = Abs x (alphaReduce t old new)
alphaReduce (App t1 t2) old new =
    App (alphaReduce t1 old new) (alphaReduce t2 old new)
-------------------------------------------------------------------------

-- Q7)
-- Beta reduction with alpha renaming to avoid variable capture (same as Q5 code)
betaReduceWithAlpha (App (Abs x t1) t2) = betaReduceWithAlpha (substitute t1 x t2)
betaReduceWithAlpha (App t1 t2) = App (betaReduceWithAlpha t1) (betaReduceWithAlpha t2)
betaReduceWithAlpha (Abs x t) = Abs x (betaReduceWithAlpha t)
betaReduceWithAlpha t = t  -- Variables remain unchanged
