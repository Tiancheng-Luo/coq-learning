
a_to_b_to_a :: a -> b -> a
a_to_b_to_a x y = x

k = a_to_b_to_a

-- const
-- K combinator

complicated :: (a -> b -> c) -> (a -> b) -> a -> c
complicated fabc fab va = fabc va (fab va)

s = complicated

-- S combinator

-- I combinator
id :: a -> a
id x = x

--
-- Proving a -> a. We look as s (with c = a).
-- 1. a -> b -> a this is k.
-- s k :: (a -> b) -> a -> a
--
-- 2. We need a -> b (for any b!). k :: a -> (b' -> a)
-- (s k) k :: a -> a

id' :: a -> a
id' = s k k

