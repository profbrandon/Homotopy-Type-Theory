
module Main 
  ( main )
where

import Prelude hiding (parse)
import System.Console.Haskeline(InputT(..), runInputT, defaultSettings, getInputLine, outputStrLn)
import System.Environment(getArgs)
import System.Directory(doesFileExist) 
import Data.List (isPrefixOf)

import Utils
import Typing
import Printing
import Parser

main :: IO ()
main = do
  args <- getArgs
  if null args
    then runInputT defaultSettings (loop "")
    else do
      bs <- mapM (doesFileExist) args
      if and bs
        then do
          str <- getFiles args
          runInputT defaultSettings (loop str)
        else error "not all files exist"
  where
    loop :: String -> InputT IO ()
    loop pre = do
      minput <- getInputLine "HoTT> "
      case minput of
        Nothing     -> return ()
        Just "quit" -> return ()
        Just txt    ->
          case txt of
            ':':txt' ->
              case () of _
                           | "exit"   `isPrefixOf` txt' -> do return ()
                           | "typeof" `isPrefixOf` txt' ->
                             case computeVal (init pre ++ ' ':(drop 6 txt')) of
                               Left  e -> do outputStrLn e; loop pre
                               Right t -> do outputStrLn $ show t; loop pre
                           | otherwise -> do outputStrLn "Error:  unrecognized command"; loop pre
            _ -> do outputStrLn "Error:  no command given"; loop pre

getFiles :: [String] -> IO String
getFiles [] = return ""
getFiles (f:fs) = do
  s <- readFile f
  ss <- getFiles fs
  return $ s ++ ss

computeVal :: String -> Either String Type
computeVal s = 
  case parseWit s of
    Left e  -> Left $ "Parsing Error:  " ++ show e
    Right w -> 
      case typeof w of
        Left e -> Left $ "Typing Error:  " ++ show e
        Right t -> Right t