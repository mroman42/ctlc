import Control.Monad

newtype Parser a = Parser (String -> [(a,String)])

parse :: Parser a -> String -> [(a,String)]
parse (Parser p) = p

instance Functor Parser where
  fmap f p = Parser (\s -> [(f x, s') | (x,s') <- parse p s])

instance Applicative Parser where 
    pure = return
    (<*>) = ap

instance Monad Parser where
  return x = Parser (\s -> [(x,s)])
  p >>= q  = Parser (\s -> concat [parse (q x) s' | (x,s') <- parse p s ])

item :: Parser Char
item = Parser (\s -> case s of
                       "" -> []
                       (c:s') -> [(c,s')])

many :: Parser a -> Parser [a]
many p = do
  a  <- p
  as <- many p
  return (a:as)

main = return ()
