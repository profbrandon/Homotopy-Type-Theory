
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
  hFiles args

loop :: String -> [String] -> InputT IO ()
loop pre files = do
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
                          case computeVal (pre ++ ' ':(drop 6 txt')) of
                            Left  e -> do outputStrLn e; loop pre files
                            Right t -> do outputStrLn $ show t; loop pre files
                        | otherwise -> do outputStrLn "Error:  unrecognized command"; loop pre files
        _ -> do outputStrLn "Error:  no command given"; loop pre files

hFiles :: [String] -> IO ()
hFiles files
  | null files = runInputT defaultSettings (loop "" files)
  | otherwise = do
    bs <- mapM doesFileExist files
    if and bs
      then do
        str <- getFiles files
        runInputT defaultSettings (loop str files)
      else do
        let bad = filter (\(b, _) -> not b) $ zip bs files
        mapM (\f -> putStrLn $ "File does not exist:  " ++ f) $ snd $ unzip bad
        return ()

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