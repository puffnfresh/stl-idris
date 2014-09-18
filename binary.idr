module binary

-- Binary literals
-- Motivation: expressiveness

data BinChar : Char -> Type where
  O : BinChar '0'
  I : BinChar '1'

data Every : (a -> Type) -> List a -> Type where
  Nil : {P : a -> Type} -> Every P []
  (::) : {P : a -> Type} -> P x -> Every P xs -> Every P (x :: xs)

fromBinChars : Every BinChar xs -> Nat -> Nat
fromBinChars [] _ = 0
fromBinChars (O :: ys) k = fromBinChars ys (k - 1)
fromBinChars (I :: ys) k = pow 2 k + fromBinChars ys (k - 1)

b : (s : String) -> {auto p : Every BinChar (unpack s)} -> Nat
b {p} s = fromBinChars p (length s - 1)

example1 : b"101" = 5
example1 = refl
