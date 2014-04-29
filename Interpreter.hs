module Interpreter where

import AbsCMinus
import qualified Data.Map as M
import Control.Monad.Error
import Control.Monad.State 
import System.IO
import Text.Read (readMaybe)

type Loc = Integer

data Env = Env {
    envV :: M.Map Ident Loc,
    envF :: M.Map Ident Func
} deriving (Show)

data Stat = Stat {
    freeLoc :: Loc,
    stateV :: M.Map Loc Val,
    retVal :: Val,
    wasBreak :: Bool,
    wasCont :: Bool,
    wasRet :: Bool
} deriving (Show)


emptyEnv = Env M.empty M.empty

emptyStat = Stat 1 M.empty NullV False False False


data Val =
      IntV Integer
    | BoolV Bool
    | ArrV (M.Map Integer Val)
    | NullV

emptyArr :: Integer -> Type -> Inter Val
emptyArr n t = case t of
    TInt -> do return $ ArrV $ M.fromList $ zip [0..n-1] (repeat (IntV 0))
    TBool -> do return $ ArrV $ M.fromList $ zip [0..n-1] (repeat (BoolV False))
    tt -> do throwError $ Err (-1) $ "There can be only maps of type Int or bool, got: " ++ (show tt)

instance Eq Val where
    (==) (IntV a) (IntV b) = a == b
    (==) (BoolV a) (BoolV b) = a == b
    (==) (NullV) (NullV) = True
    (==) _ _ = False

instance Show Val where
    show (IntV a) = show a
    show (BoolV a) = show a
    show (NullV) = "Null"

data Func = Func {
    fId :: Ident,
    fPars :: [Ident], 
    fBlock :: Block,
    fEnv :: Env
} deriving (Show)


data IError = Err {
    location :: Int,
    message  :: String
}

instance Show IError where
    show e = show $ show (location e) ++ ": " ++ message e

instance Error IError where
    noMsg = Err (-1) "Runtime Error"
    strMsg s = Err (-1) s


type Inter a = StateT Stat (ErrorT IError IO) a


runInter i s =
    (runErrorT $ runStateT i s) >>= (\x -> case x of
        Left msg -> putStrLn $ message msg
        Right (a, st) -> putStr "" )

go :: Program -> IO()
go tree = runInter (runProg' tree emptyEnv) emptyStat

runProg' :: Program -> Env -> Inter ()
runProg' p e = (runProg p e) `catchError` handler where
    handler er = throwError $ Err (-1) $ "Runtime Error: \n" ++ (show er)

runProg :: Program -> Env -> Inter ()
runProg (Prog decs funs) env = do
    env1 <- runDecls decs env
    env2 <- runFuns funs env1
    runExp (ECall (Ident "main") []) env2
    return ()

runDecls :: [Decl] -> Env -> Inter Env
runDecls [] env = do 
    return env
runDecls (d:decs) env = case d of
    DVarInit t i e -> do
        env1 <- runDVarInit d env
        runDecls decs env1
    DVar t i -> case t of 
        TInt -> do
            env1 <- runDVarInit (DVarInit t i (EInt 0)) env
            runDecls decs env1
        TBool -> do
            env1 <- runDVarInit (DVarInit t i (EFalse)) env
            runDecls decs env1
    DArray t i n -> do
        env1 <- runDArr (DArray t i n) env
        runDecls decs env1

runDArr :: Decl -> Env -> Inter Env
runDArr (DArray t i n) env = do
    stat <- get
    let loc = freeLoc stat
    arr <- emptyArr n t
    put stat {stateV = M.insert loc arr (stateV stat), freeLoc = loc + 1}
    return env {envV = M.insert i loc (envV env)}

runDVarInit :: Decl -> Env -> Inter Env
runDVarInit (DVarInit t i e) env = do
    val <- runExp e env
    stat <- get
    let loc = freeLoc stat
    put stat {stateV = M.insert loc val (stateV stat), freeLoc = loc + 1}
    return env {envV = M.insert i loc (envV env)}

runFuns :: [Function] -> Env -> Inter Env
runFuns [] env = do 
    return env
runFuns (f:funs) env = case f of
    Fun t id pars blck -> do
        let p = getParIds pars
        runFuns funs env {envF = M.insert id (Func id p blck env) (envF env)}         

getParIds :: [Par] -> [Ident]
getParIds [] = []
getParIds ((PVar t id):ps) = id:(getParIds ps)
getParIds ((PArr t id):ps) = id:(getParIds ps)

runExp :: Exp -> Env -> Inter Val
runExp e env = case e of
    EInt x -> return (IntV x)
    EAdd e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	return (IntV (v1 + v2))        
    ESub e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	return (IntV (v1 - v2))        
    EMul e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	return (IntV (v1 * v2))        
    EDiv e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	if v2 == 0
            then throwError $ Err (-1) $ "Division by 0! Zero value of expression: " ++ (show e2)
	    else return (IntV (v1 `div` v2))        
    EMod e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	if v2 == 0
            then throwError $ Err (-1) $ "Mod by 0! Zero value of expression: " ++ (show e2)
            else return (IntV (v1 `mod` v2))        
    ETrue -> return (BoolV True)
    EFalse -> return (BoolV False)
    EAnd e1 e2 -> do
        BoolV v1 <- runExp e1 env
        BoolV v2 <- runExp e2 env
	return (BoolV (v1 && v2))        
    EOr e1 e2 -> do
        BoolV v1 <- runExp e1 env
        BoolV v2 <- runExp e2 env
	return (BoolV (v1 || v2))        
    EEq e1 e2 -> do
        v1 <- runExp e1 env
        v2 <- runExp e2 env
	return (BoolV (v1 == v2))        
    ENeq e1 e2 -> do
        v1 <- runExp e1 env
        v2 <- runExp e2 env
	return (BoolV (v1 /= v2))        
    ELt e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	return (BoolV (v1 < v2))        
    EGt e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	return (BoolV (v1 > v2))        
    ELeq e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	return (BoolV (v1 <= v2))        
    EGeq e1 e2 -> do
        IntV v1 <- runExp e1 env
        IntV v2 <- runExp e2 env
	return (BoolV (v1 >= v2))        
    EGet -> do
        str <- liftIO getLine
        case readMaybe str :: Maybe Integer of
            Just x -> do return (IntV x)
            Nothing -> do throwError $ Err (-1) $ "Wrong input, expected Integer, got: " ++ str 
    ENot e1 -> do 
        BoolV v1 <- runExp e1 env
        return (BoolV (not v1))
    ENeg e1 -> do 
        IntV v1 <- runExp e1 env
        return (IntV (0 - v1))
    EAssVar id op e1 ->
        case op of
            Assign -> do
                v1 <- runExp e1 env
                loc <- findVarLoc id env
                stat <- get
                put stat {stateV = M.insert loc v1 (stateV stat)}   
                return v1
            _ -> do
                IntV val <- findVarVal id env
                IntV v1 <- runExp e1 env
		if (v1 == 0 && (op == AssignDiv || op == AssignMod))
		    then do throwError $ Err (-1) $ "Div or mod by 0! Zero value of expression: " ++ (show e1)
                    else do  
                        loc <- findVarLoc id env
                        f <- getOp op
                        let v2 = (IntV (f val v1 ))
                        stat <- get
                        put stat {stateV = M.insert loc v2 (stateV stat)}   
                        return v2
    EPreInc e1 -> 
        case e1 of
            EVar id -> do
                loc <- findVarLoc id env
                IntV val <- findVarVal id env
                stat <- get
                put stat {stateV = M.insert loc (IntV (val + 1)) (stateV stat)}
                return (IntV (val + 1))
            eee -> do throwError $ Err (-1) $ "Expected variable argument (Evar) for ++_ operator, got: " ++ show(eee)
    EPreDec e1 -> 
        case e1 of
            EVar id -> do
                loc <- findVarLoc id env
                IntV val <- findVarVal id env
                stat <- get
                put stat {stateV = M.insert loc (IntV (val - 1)) (stateV stat)}
                return (IntV (val - 1))
            eee -> do throwError $ Err (-1) $ "Expected variable argument (Evar) for --_ operator, got: " ++ show(eee)
    EPostInc e1 -> 
        case e1 of
            EVar id -> do
                loc <- findVarLoc id env
                IntV val <- findVarVal id env
                stat <- get
                put stat {stateV = M.insert loc (IntV (val + 1)) (stateV stat)}
                return (IntV val)
            eee -> do throwError $ Err (-1) $ "Expected variable argument (Evar) for _++ operator, got: " ++ show(eee)
    EPostDec e1 ->
        case e1 of
            EVar id -> do
                loc <- findVarLoc id env
                IntV val <- findVarVal id env
                stat <- get
                put stat {stateV = M.insert loc (IntV (val - 1)) (stateV stat)}
                return (IntV val)
            eee -> do throwError $ Err (-1) $ "Expected variable argument (Evar) for _-- operator, got: " ++ show(eee)

    ECall id args -> do
        (Func fid fpar fblo fenv) <- findFun id env
        env1 <- bindArgs args fpar env fenv
        runBlock fblo env1 {envF = M.insert fid (Func fid fpar fblo fenv) (envF env1)}
        stat <- get
        let rv = retVal stat
        put stat {retVal = NullV}
        return rv
    EVar id -> do 
        findVarVal id env
    EArray id e1 -> do
        IntV v1 <- runExp e1 env
        ArrV arr <- findVarVal id env
        if v1 < 0 || v1 > (toInteger (M.size arr)) - 1
            then do throwError $ Err (-1) $ "Index (" ++ (show v1) ++ ") out of bounds: 0 - " ++ (show (M.size arr))
            else case M.lookup v1 arr of
                Just x -> do return x
                _ -> do throwError $ Err (-1) $ "EArray - sth gone terribly wrong" 
    EAssArr id e1 op e2 -> do
        IntV v1 <- runExp e1 env
        ArrV arr <- findVarVal id env
        loc <- findVarLoc id env
        if v1 < 0 || v1 > (toInteger (M.size arr)) - 1
            then do throwError $ Err (-1) $ "Index (" ++ (show v1) ++ ") out of bounds: 0 - " ++ (show (M.size arr))
            else case op of
                Assign -> do 
                    v2 <- runExp e2 env
                    stat <- get
                    put stat {stateV = M.insert loc (ArrV (M.insert v1 v2 arr)) (stateV stat)}
                    return v2
                _ -> do
                    IntV val <- runExp (EArray id e1) env
                    IntV v2 <- runExp e2 env
		    if (v2 == 0 && (op == AssignDiv || op == AssignMod))
		        then do throwError $ Err (-1) $ "Div or mod by 0! Zero value of expression: " ++ (show e1)
                        else do  
                            f <- getOp op
                            let v3 = (IntV (f val v2 ))
                            stat <- get
                            put stat {stateV = M.insert loc (ArrV (M.insert v1 v3 arr)) (stateV stat)}
                            return v3
    eee -> do
        throwError $ Err (-1) $ "Unimplemented expression: " ++ (show eee)

bindArgs :: [Arg] -> [Ident] -> Env -> Env -> Inter Env
bindArgs [] [] _ fenv = do return fenv
bindArgs (a:args) (id:ids) env fenv = do
    fenv1 <- bindArg a id env fenv
    bindArgs args ids env fenv1
bindArgs (a:args) [] _ _ = do throwError $ Err (-1) $ "Too many arguments passed to a function. Redundant argument: " ++ (show a)
bindArgs [] (id:ids) _ _ = do throwError $ Err (-1) $ "Missing arguments in function call. Missing argument: " ++ (show id)

bindArg :: Arg -> Ident -> Env -> Env -> Inter Env
bindArg a id env fenv = case a of
    AVal e1 -> do
        val <- runExp e1 env
        stat <- get
        let loc = freeLoc stat
        put stat {stateV = M.insert loc val (stateV stat), freeLoc = loc + 1}
        return fenv {envV = M.insert id loc (envV fenv)}
    ARef nam -> do
        loc <- findVarLoc nam env
        return fenv {envV = M.insert nam loc (envV fenv)}

getOp :: AssOp -> Inter (Integer -> Integer -> Integer)
getOp op = case op of
    AssignMod -> return $ mod
    AssignDiv -> return $ div
    AssignAdd -> return $ (+)
    AssignSub -> return $ (-)
    AssignMul -> return $ (*)


findVarVal :: Ident -> Env -> Inter Val
findVarVal id env = do
    loc <- findVarLoc id env
    val <- findLocVal loc
    return val

findVarLoc :: Ident -> Env -> Inter Loc
findVarLoc id env = do
    let loc = M.lookup id (envV env)
    case loc of 
        Just l -> return l
        _ -> throwError $ Err (-1) $ "Undefined variable: " ++ (show id)

findLocVal :: Loc -> Inter Val
findLocVal l = do
    stat <- get
    let val = M.lookup l (stateV stat)
    case val of
        Just v -> return v
        _ -> throwError $ Err (-1) $ "No value stored under location: " ++ (show l)

runBlock :: Block -> Env -> Inter ()
runBlock (Block ds fs stms) env = do 
    env1 <- runDecls ds env
    env2 <- runFuns fs env1
    runStms stms env2

findFun :: Ident -> Env -> Inter Func
findFun id env = do 
    let f = M.lookup id (envF env)
    case f of
       Just ff -> return ff
       _ -> throwError $ Err (-1) $ "Undefined function: " ++ (show id)       

runStms :: [Stm] -> Env -> Inter ()
runStms [] _ = do return ()
runStms (s:stms) env = do
    runStm s env
    runStms stms env

runStm :: Stm -> Env -> Inter ()
runStm stm env = case stm of
    SNull -> return ()
    SExp e -> do
        runExp e env
        runStm SNull env
    SPrint e -> do
        val <- runExp e env
        liftIO $ putStrLn (show val)
        liftIO $ hFlush stdout
    SBlock b -> do
        runBlock b env
    SIf e s1 -> do
        BoolV b <- runExp e env
        if b 
            then runStm s1 env
            else runStm SNull env
    SIfElse e s1 s2 -> do
        BoolV b <- runExp e env
        if b 
            then runStm s1 env
            else runStm s2 env
    SWhile e s1 -> do
        BoolV b <- runExp e env
        if b
            then do 
                runStm s1 env
                runStm (SWhile e s1) env
            else do
                runStm SNull env
    SDoWhile s1 e -> do 
        runStm s1 env
        runStm (SWhile e s1) env
    SFor d1 e1 e2 s1 -> do
	env1 <- runDecls [d1] env
	runStm (SWhile e1 (SBlock (Block [] [] [s1, (SExp e2)]))) env1
    SRepeat e1 s1 -> do
        let nid = (Ident "losowy14524326") 
	runStm (SFor (DVarInit TInt nid e1) (EGt (EVar nid) (EInt 0)) (EPreDec (EVar nid)) s1) env
    --SBreak -> checkBCR $ modify (\en -> en{wasBreak = True})    -- USTAWIC flage break , a w pętli ja czyscic przy kazdym obrocie, przed kazdym statesmentem sprawdzamy, czy ktoras ustawiona.
    --SContinue
    SRetNull -> do
        stat <- get
        put stat {retVal = NullV}
        runStm SNull env
    SRetVal e1 -> do
        v1 <- runExp e1 env
        stat <- get
        put stat {retVal = v1}
        runStm SNull env
    SAssert e1 -> do
        BoolV v1 <- runExp e1 env
        if v1 
            then do runStm SNull env
            else do throwError $ Err (-1) $ "Assertion failed! Expression " ++ (show e1) ++ " returned false."       


--checkBCR ss = do
    

