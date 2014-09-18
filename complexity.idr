module complexity

-- Computation complexity
-- Motivation: coworker

data Cost : Nat -> Type -> Type where
  MkCost : t -> Cost n t

uncost : Cost n t -> t
uncost (MkCost x) = x

return : t -> Cost n t
return x = MkCost x

(>>=) : Cost n a -> (a -> Cost m b) -> Cost (n + m) b
(>>=) (MkCost x) f = MkCost (uncost (f x))

doTimes : Semigroup a =>
          (n : Nat) ->
          Cost m a ->
          a ->
          Cost (n * m) a
doTimes Z _ accum = return accum
doTimes (S k) cost accum = do
  a <- cost
  doTimes k cost (accum <+> a)

day : (n : Nat) -> Cost (fact n) String
day Z = return "."
day (S k) = doTimes (S k) (day k) "$"

run : (n : Fin 7) -> Cost (fact (finToNat n)) String
run n = day (finToNat n)



f : Cost 2 String
f = return "Hello Daniel"

g : Cost ?todo String
g = f

todo = proof search

h : Cost 3 String
h = g
