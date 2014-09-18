module binary

%default total

data BinChar : (Char -> Type) where
  O : BinChar '0'
  I : BinChar '1'

data Every : (a -> Type) -> List a -> Type where
  Nil : {P : a -> Type} -> Every P []
  (::) : {P : a -> Type} -> P x -> Every P xs -> Every P (x :: xs)

fromBinChars : Every BinChar l -> Nat -> Nat
fromBinChars [] _ = 0
fromBinChars (O :: xs) n = fromBinChars xs (n - 1)
fromBinChars (I :: xs) n = pow 2 n + fromBinChars xs (n - 1)

b : (s : String) -> {auto p : Every BinChar (unpack s)} -> Nat
b {p} s = fromBinChars p (length s - 1)
