module Utils where
import Data.List

doubles :: Eq a => [a] -> [a]
doubles [] = []
doubles (x:xs) = if x `elem` xs then x:doubles (deleteAll x xs) else doubles xs

deleteAll :: Eq a => a -> [a] -> [a]
deleteAll _ [] = []
deleteAll x xs = if length xs' == length xs then xs else deleteAll x xs'
       where xs' = delete x xs
