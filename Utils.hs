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

isSubsetOf :: Eq a => [a] -> [a] -> Bool
isSubsetOf [] _ = True
isSubsetOf (x:xs) ys = if x `elem` ys then xs `isSubsetOf` ys else False

counts :: Eq a => Ord a => [a] -> [(Int, a)]
counts xs = countsAux (sort xs) []

countsAux :: Eq a => [a] -> [(Int, a)] -> [(Int, a)]
countsAux [] prev = prev
countsAux (x:xs) prev =
       case mi of Nothing -> countsAux xs ((1, x):prev)
                  Just i -> let (n, y) = prev !! i
                                (lft, rht) = splitAt i prev
                             in countsAux xs (init lft ++ (n+1, y):rht)
       where
              mi = findIndex (\(_, y) -> x == y) prev
