module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )

import LexCMinus
import ParCMinus
import PrintCMinus
import AbsCMinus

import TypeChecker
import Interpreter

import ErrM

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = readFile f >>= run v p

run :: Verbosity -> ParseFun Program -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn s
           Ok  tree -> do 
                          putStrV v "\nParse Successful!"
                          putStrV v "\nChecking types..."
                          case checktypes tree of 
                              Nothing -> do
                                  (showTree v tree)
                                  putStrV v "Checking types successful!"
                                  putStrV v "Running program..."
                                  go tree
                              Just x -> putStrLn x
 


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

printHelp :: IO()
printHelp = do
    nam <- getProgName
    putStrLn $ "Usage: " ++ nam ++ " [-v] " ++ "<file_path>"
    


main :: IO ()
main = do args <- getArgs
          case args of
            [] -> printHelp
            "-v":fs:[] -> runFile 2 pProgram fs
            fs:[] -> runFile 0 pProgram fs
            _ -> printHelp





