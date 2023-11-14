module Utils where
import Data.List

-- returns only duplicated elements
doubles :: Eq a => [a] -> [a]
doubles [] = []
doubles (x:xs) = if x `elem` xs then x:doubles (deleteAll x xs) else doubles xs

-- deletes all occurrences of the specified element in the list
deleteAll :: Eq a => a -> [a] -> [a]
deleteAll _ [] = []
deleteAll x xs = if length xs' == length xs then xs else deleteAll x xs'
       where xs' = delete x xs

allEqual :: Eq a => [a] -> Bool
allEqual [] = True
allEqual [x] = True
allEqual (x:x':xs) = x == x' && allEqual (x':xs)