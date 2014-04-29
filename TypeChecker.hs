module TypeChecker (checktypes) where

import AbsCMinus
import qualified Data.Map as M
import Control.Monad.Error
import Control.Monad.State 
import System.IO
import Text.Read (readMaybe)


type TCM a = StateT Env2 (Either String) a
type Env2 = M.Map Ident CType

data Env = Env {
    cenv :: M.Map Ident CType,
    retType :: Type
}

emptyEnv = Env M.empty TVoid

data CType = 
      VarT Type 
    | FunT Type [Par]
    | ArrT Type
    deriving (Eq,Ord,Show)

checktypes :: Program -> Maybe String
checktypes p = case evalStateT (tcheck' p emptyEnv) M.empty of
                                        Left s -> Just s
                                        _ -> Nothing

tcheck' :: Program -> Env -> TCM ()
tcheck' p env = (tcheck p env) `catchError` handler where
    handler e = throwError $ "Type Error:\n" ++ (show e)

tcheck :: Program -> Env -> TCM ()
tcheck (Prog decls funcs) env = do 
    env1 <- chDecls decls env
    env2 <- chFuns funcs env1
    let mains = length (filter isMain funcs)
    if mains /= 1 
        then do throwError $ "There must be exacly one main function of type void, found: " ++ (show mains)
        else do return ()

isMain :: Function -> Bool
isMain (Fun t id _ _) = ((t == TVoid) && (id == (Ident "main")))

isRetVal :: Stm -> Bool
isRetVal s = case s of
    (SRetVal _) -> True
    _ -> False

chReturns :: Type -> Block -> TCM ()
chReturns TVoid _ = do return ()
chReturns t (Block _ _ stms) = do 
    let rets = length (filter isRetVal stms)
    if rets < 1
        then do throwError $ "No return statement with value in function with expected return type " ++ (show t)
        else do return ()

par2decl :: [Par] -> [Decl]
par2decl [] = []
par2decl ((PVar t id):ps) = (DVar t id):(par2decl ps)
par2decl ((PArr t id):ps) = (DArray t id 1):(par2decl ps)

chFuns :: [Function] -> Env -> TCM Env
chFuns [] env = do return env
chFuns (f:funs) env = case f of
    Fun t id params blck -> do
        let env1 = env {cenv = M.insert id (FunT t params) (cenv env)}
	env2 <- chDecls (par2decl params) env1
        chReturns t blck
        chBlock blck env2 {retType = t}
        chFuns funs env1 

chBlock :: Block -> Env -> TCM ()
chBlock (Block ds fs stms) env = do 
    env1 <- chDecls ds env
    env2 <- chFuns fs env1
    chStms stms env2

chStms :: [Stm] -> Env -> TCM ()
chStms [] _ = do return ()
chStms (s:stms) env = do
    chStm s env
    chStms stms env

chStm :: Stm -> Env -> TCM ()
chStm stm env = case stm of
    SNull -> return ()
    SExp e -> do
        typeofExp e env
        chStm SNull env
    SPrint e -> do
        typeofExp e env
        chStm SNull env

    SBlock b -> do
        chBlock b env
    SIf e s1 -> do
        t1 <- typeofExp e env
	if t1 /= TBool 
            then do throwError $ "Expected expression with bool result, got " ++ (show t1)
            else do chStm s1 env
    SIfElse e s1 s2 -> do
        t1 <- typeofExp e env
	if t1 /= TBool 
            then do throwError $ "Expected expression with bool result, got " ++ (show t1)
            else do 
                chStm s1 env
                chStm s2 env
    SWhile e s1 -> do
        t1 <- typeofExp e env
	if t1 /= TBool 
            then do throwError $ "Expected expression with bool result, got " ++ (show t1)
            else do chStm s1 env
    SDoWhile s1 e -> do 
        t1 <- typeofExp e env
	if t1 /= TBool 
            then do throwError $ "Expected expression with bool result, got " ++ (show t1)
            else do chStm s1 env
    SFor d1 e1 e2 s1 -> do
        env1 <- chDecls [d1] env
        t1 <- typeofExp e1 env1
	if t1 /= TBool 
            then do throwError $ "Expected expression with bool result, got " ++ (show t1)
            else do
                typeofExp e2 env1 
                chStm s1 env1
    SRepeat e1 s1 -> do
        t1 <- typeofExp e1 env
	if t1 /= TInt 
            then do throwError $ "Expected expression with int result, got " ++ (show t1)
            else do chStm s1 env
    --SBreak -> checkBCR $ modify (\en -> en{wasBreak = True})
    --SContinue
    SRetNull -> case retType env of  
        TVoid -> do chStm SNull env
        x -> do throwError $ "Return with no value from function with expected return type: " ++ (show x)
    SRetVal e1 -> do
        t1 <- typeofExp e1 env
	let t2 = retType env
        if t1 == t2
            then do chStm SNull env
            else do throwError $ "Returned value of type " ++ (show t1) ++ " from function with expected return type " ++ (show t2)
    SAssert e1 -> do
        t1 <- typeofExp e1 env
	if t1 /= TBool 
            then do throwError $ "Expected expression with bool result, got " ++ (show t1)
            else do chStm SNull env

chVoid :: Ident -> CType -> TCM ()
chVoid id t = do  
    if t == (VarT TVoid)
        then do throwError $ "Variable " ++ (show id) ++ " of type void."
        else do return ()


chDecls :: [Decl] -> Env -> TCM Env
chDecls [] env = do return env
chDecls (d:decs) env = case d of
    DVarInit t i e -> do
        chVoid i (VarT t)
	te <- typeofExp e env
        if te /= t 
            then do throwError $ "Declared type of " ++ (show i) ++  " :: " ++ (show t) ++ " and assigned value: " ++ (show te) ++ " mismatch."
            else do 
                chDecls decs env {cenv = M.insert i (VarT t) (cenv env)}
    DVar t i -> case t of
	TInt -> do chDecls ((DVarInit t i (EInt 0)):decs) env
	TBool -> do chDecls ((DVarInit t i (EFalse)):decs) env
    DArray t i n -> do
        chVoid i (ArrT t)
        chDecls decs env {cenv = M.insert i (ArrT t) (cenv env)}


typeofExp :: Exp -> Env -> TCM Type
typeofExp (EInt _) _ = do return TInt
typeofExp (EVar id) env = do 
    case M.lookup id (cenv env) of
        Just (VarT t) -> do return t
        _ -> do throwError $ "Undeclared variable " ++ (show id)
typeofExp (ETrue) _ = return TBool
typeofExp (EFalse) _ = return TBool
typeofExp (EGet) _ = return TInt
typeofExp (ENot e1) env = do
    t1 <- typeofExp e1 env
    case t1 of
        TBool -> do return TBool
        x -> do throwError $ "Expected expression of type TBool in negation, got: " ++ (show x)
typeofExp (ENeg e1) env = do
    t1 <- typeofExp e1 env
    case t1 of
        TInt -> do return TInt
        x -> do throwError $ "Expected expression of type TInt in negation, got: " ++ (show x)
typeofExp (EOr e1 e2) env= do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TBool && t2 == TBool)
        then do return TBool
        else do throwError $ "Expected two expressions of type TBool in logic OR, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EAnd e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TBool && t2 == TBool)
        then do return TBool
        else do throwError $ "Expected two expressions of type TBool in logic AND, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (ELt e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TBool
        else do throwError $ "Expected two expressions of type TInt in comparison expresion _<_, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EGt e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TBool
        else do throwError $ "Expected two expressions of type TInt in comparison expresion _>_, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (ELeq e1 e2) env= do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TBool
        else do throwError $ "Expected two expressions of type TInt in comparison expresion _<=_, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EGeq e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TBool
        else do throwError $ "Expected two expressions of type TInt in comparison expresion _>=_, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EPostInc e1) env= do
    t1 <- typeofExp e1 env
    case t1 of
        TInt -> do return TInt
        x -> do throwError $ "Expected expression of type TInt in postincrementation, got: " ++ (show x)
typeofExp (EPostDec e1) env = do
    t1 <- typeofExp e1 env
    case t1 of
        TInt -> do return TInt
        x -> do throwError $ "Expected expression of type TInt in postdecrementation, got: " ++ (show x)
typeofExp (EPreInc e1) env = do
    t1 <- typeofExp e1 env
    case t1 of
        TInt -> do return TInt
        x -> do throwError $ "Expected expression of type TInt in preincrementation, got: " ++ (show x)
typeofExp (EPreDec e1) env = do
    t1 <- typeofExp e1 env 
    case t1 of
        TInt -> do return TInt
        x -> do throwError $ "Expected expression of type TInt in predecrementation, got: " ++ (show x)
typeofExp (EAdd e1 e2) env = do
    t1 <- typeofExp e1 env 
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TInt
        else do throwError $ "Expected two expressions of type TInt in addition, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (ESub e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TInt
        else do throwError $ "Expected two expressions of type TInt in subtraction, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EMul e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TInt
        else do throwError $ "Expected two expressions of type TInt in multiplication, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EDiv e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TInt
        else do throwError $ "Expected two expressions of type TInt in division, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EMod e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == TInt && t2 == TInt)
        then do return TInt
        else do throwError $ "Expected two expressions of type TInt in modulo, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EEq e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == t2)
        then do return TBool
        else do throwError $ "Type mismatch in == expression, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (ENeq e1 e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    if (t1 == t2)
        then do return TBool
        else do throwError $ "Type mismatch in != expression, got: " ++ (show t1) ++ " and " ++ (show t2)
typeofExp (EAssVar id op e1) env = do
    t1 <- typeofExp e1 env
    case M.lookup id (cenv env) of
        Just (VarT t) -> case t of
            TBool -> if (t1 == TBool && op == Assign) 
                then do return TBool
                else do throwError $ "Type mismatch or forbidden assignment operator for bool arument: " ++ (show t1) ++ " " ++ (show t) ++ " " ++ (show op)
            TInt -> if t1 == TInt
                then do return TInt
                else do throwError $ "Type mismatch in assignment: " ++ (show t1) ++ " " ++ (show t)
        _ -> do throwError $ "Undeclared variable " ++ (show id)
typeofExp (ECall id args) env = do
    case M.lookup id (cenv env) of
        Just (FunT t pars) -> do 
            compareArgPar args pars env
            return t
        _ -> do throwError $ "Undeclared function " ++ (show id)
typeofExp (EArray id e1) env = do
    t1 <- typeofExp e1 env
    case M.lookup id (cenv env) of
        Just (ArrT t) -> if t1 == TInt
            then do return t
            else do throwError $ "Array index must be of type int, got " ++ (show t1)
        _ -> do throwError $ "Undeclared array " ++ (show id)
typeofExp (EAssArr id e1 op e2) env = do
    t1 <- typeofExp e1 env
    t2 <- typeofExp e2 env
    case M.lookup id (cenv env) of
        Just (ArrT t) -> do 
            if t1 == TInt
                then do 
                    if t2 == t
                        then do return t
                        else do throwError $ "Type mismatch in assignment, expected " ++ (show t) ++ ", got " ++ (show t2)
                else do throwError $ "Array index must be of type int, got " ++ (show t1) 
        _ -> do throwError $ "Undeclared array " ++ (show id)

compareArgPar :: [Arg] -> [Par] -> Env -> TCM ()
compareArgPar [] [] _ = do return ()
compareArgPar (a:args) [] _ = do throwError $ "Too man arguments passed to a function. Redundant argument: " ++ (show a)
compareArgPar [] (p:pars) _ = do throwError $ "Too little arguments passed to a function. Unsatisfied parameter: " ++ (show p)
compareArgPar ((AVal e1):args) ((PVar t id):pars) env = do
    t1 <- typeofExp e1 env
    if t1 == t
        then do compareArgPar args pars env
        else do throwError $ "Passed argument of type " ++ (show t1) ++ " to function, expected type: " ++ (show t)
compareArgPar ((ARef aid):args) ((PVar t pid):pars) env = do
    case M.lookup aid (cenv env) of
        Just (VarT t1) -> do 
            if t1 == t
                then do compareArgPar args pars env
                else do throwError $ "Passed argument of type " ++ (show t1) ++ " to function, expected type: " ++ (show t)
        _ -> do throwError $ "Undeclared variable " ++ (show aid) ++ " passed by reference to a function"
    
--TODO
compareArgPar a p e =  do throwError $ "Argument/parameter mismatch " ++ (show a) ++ " and " ++ (show p)


{-
 | EContains Ident Exp
-}
