module algebraic

-- Algebraic laws
-- Motivation: correctness

data Bit = O | I

or : Bit -> Bit -> Bit
or O x1 = x1
or I x1 = I

-- (a `or` b) `or` c = a `or` (b `or` c)

orAssociative : (a : Bit) ->
                (b : Bit) ->
                (c : Bit) ->
                (a `or` b) `or` c = a `or` (b `or` c)
orAssociative O b c = refl
orAssociative I b c = refl

BitString : Type
BitString = List Bit

bsor : BitString -> BitString -> BitString
bsor [] x1 = x1
bsor xs [] = xs
bsor (x :: xs) (y :: ys) = (x `or` y) :: (xs `bsor` ys)

bsorAssociative : (a : BitString) ->
                  (b : BitString) ->
                  (c : BitString) ->
                  (a `bsor` b) `bsor` c = a `bsor` (b `bsor` c)
bsorAssociative [] b c = refl
bsorAssociative (x :: xs) [] c = refl
bsorAssociative (x :: xs) (y :: ys) [] = refl
bsorAssociative (x :: xs) (y :: ys) (z :: zs) = ?bsorAssociative_rhs_4

---------- Proofs ----------

algebraic.bsorAssociative_rhs_4 = proof
  intros
  rewrite orAssociative x y z
  rewrite bsorAssociative xs ys zs
  trivial

