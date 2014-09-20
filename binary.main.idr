module Main

import binary

fromChar : (c : Char) -> Maybe (BinChar c)
fromChar '0' = Just O
fromChar '1' = Just I
fromChar _ = Nothing

fromChars : (l : List Char) -> Maybe (Every BinChar l)
fromChars [] = Just []
fromChars (x :: xs) = do
  x' <- fromChar x
  xs' <- fromChars xs
  return (x' :: xs')

fromString : (s : String) -> Maybe (Every BinChar (unpack s))
fromString s = fromChars (unpack s)

partial
main : IO ()
main = do
  putStr "Binary: "
  binary <- map trim getLine
  maybe (putStrLn "Those aint binary digits") (\ev => print (b {p=ev} binary)) (fromString binary)
