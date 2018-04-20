data Dyadic = Float Integer [Integer] | Zero

-- (+) :: Dyadic -> Dyadic -> Dyadic
-- n + Zero = n
-- Zero + m = m
-- (Float n xs) + (Float m ys) =
--   case compare n m of
--     LT -> Float n (1 : replicate (m - n) 0)
--     EQ -> Float bitwiseadd
--     GT -> Float m 


bitwiseadd :: [Bool] -> [Bool] -> [Bool]
bitwiseadd [] [] = [False]
bitwiseadd [] (False : ys) = True : ys
bitwiseadd [] (True : ys) = False : bitwiseadd [] ys
bitwiseadd (False : xs) [] = True : xs
bitwiseadd (True : xs) [] = False : bitwiseadd [] xs
bitwiseadd (False : xs) (y : ys) = y : bitwiseadd xs ys
bitwiseadd (True : xs) (False : ys) = True : bitwiseadd xs ys
bitwiseadd (True : xs) (True : ys) = False : bitwiseadd [] (bitwiseadd xs ys)

shift :: Integer -> [Bool] -> [Bool]
shift n xs = replicate (fromEnum n) False ++ xs


