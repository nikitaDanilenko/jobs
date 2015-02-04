{-\# OPTIONS\_CYMAKE -X TypeClassExtensions \#-}

The Jobs Puzzle
===============

This file is a literate Curry file. You can save it with the extension
.lcurry and load it into the most recent version (\>= 0.3.3) of the
KiCS2 compiler

``` { .literate .haskell}
import FiniteMap ( lookupFM, listToFM, FM )
import Function  ( on )
import List      ( sort )
import Maybe     ( fromMaybe )
```

``` { .literate .haskell}
import SetFunctions ( set0, values2list )
```

Relational preliminaries
------------------------

Data structure for relations over finite domains.

``` { .literate .haskell}
data Rel a b = Rel (FM (a, b) Bool) [a] [b]
```

Returns the domain of the argument relation.

``` { .literate .haskell}
firstValues :: Rel a b -> [a]
firstValues (Rel _ as _) = as
```

Returns the codomain of the argument relation.

``` { .literate .haskell}
secondValues :: Rel a b -> [b]
secondValues (Rel _ _ bs) = bs
```

Given a relation and a row "name" this function returns the
corresponding row. The computations forces a choice for non-determnistic
values.

``` { .literate .haskell}
row :: (Ord a, Ord b) => Rel a b -> a -> [b]
row (Rel fm _ bs) a = [b | b <- bs, fm ! (a, b)]
```

Given a relation and a column "name" this function returns the
corresponding column. The computations forces a choice for
non-determnistic values.

``` { .literate .haskell}
col :: (Ord a, Ord b) => Rel a b -> b -> [a]
col (Rel fm as _) b = [a | a <- as, fm ! (a, b)]
```

Checks whether all rows of a relation satisfy a given predicate.

``` { .literate .haskell}
allRows :: (Ord a, Ord b) => ([b] -> Bool) -> Rel a b -> Bool
allRows p r = all (p . row r) (firstValues r)
```

Checks whether all columns of a relations satisfy a given predicate.

``` { .literate .haskell}
allColumns :: (Ord a, Ord b) => ([a] -> Bool) -> Rel a b -> Bool
allColumns p r = all (p . col r) (secondValues r)
```

Given a FiniteMap and a key, this function looks up the value of the
key. If the key is present, the value of the key is returned, otherwise
the computation fails.

``` { .literate .haskell}
(!) :: Ord k => FM k v -> k -> v
fm ! k = fromMaybe failed (lookupFM fm k)
```

"Pretty"-prints a relation.

``` { .literate .haskell}
showRel :: (Ord a, Ord b, Show a, Show b) => Rel a b -> String
showRel r = unlines [unwords [show a, ":", show (row r a)] | a <- firstValues r]
```

Auxiliaries
-----------

Lists all values of a bounded, enumerable data type.

``` { .literate .haskell}
listAll :: (Enum a, Bounded a) => [a]
listAll = [minBound .. maxBound]
```

Checks whether a list has a given size. This check is sufficiently lazy
an works on infinite lists.

``` { .literate .haskell}
hasLength :: [a] -> Int -> Bool
hasLength []       n = n == 0
hasLength (_ : xs) n = n > 0 && hasLength xs (n - 1)
```

Checks whether two lists of comparable elements are the same when
considered as sets.

``` { .literate .haskell}
isEqual :: Ord a => [a] -> [a] -> Bool
isEqual = (==) `on` sort
```

Checks whether two lists of comparable elements are different when
considered as sets.

``` { .literate .haskell}
isNotEqual :: Ord a => [a] -> [a] -> Bool
isNotEqual xs ys = not (isEqual xs ys)
```

Given two ranges an some filled positions, this function creates a
relation whose missing positions are filled with free variables.

``` { .literate .haskell}
mkNonDetRel :: (Ord a, Ord b) => [a] -> [b] -> [((a, b), Bool)] -> Rel a b
mkNonDetRel as bs filled = Rel (listToFM (<) [((a, b), f a b) | a <- as, b <- bs]) as bs where
    f a b = fromMaybe (let x free in x) (lookup (a, b) filled)
```

This function creates a specified entry for the relation.

``` { .literate .haskell}
hasValue :: Bool -> a -> b -> ((a, b), Bool)
hasValue bool a b = ((a, b), bool)
```

This function creates a positive entry for the relation.

``` { .literate .haskell}
is :: a -> b -> ((a, b), Bool)
is = hasValue True
```

This function creates a negative entry for the relation.

``` { .literate .haskell}
isNot :: a -> b -> ((a, b), Bool)
isNot = hasValue False
```

Jobs-Puzzle
-----------

-   There are four people: Roberta, Thelma, Steve, and Pete.
-   Among them, they hold eight different jobs.
-   Each holds exactly two jobs.
-   The jobs are chef, guard, nurse, clerk, police officer (gender not
    implied), teacher, actor, and boxer.
-   The job of nurse is held by a male.
-   The husband of the chef is the clerk.
-   Roberta is not a boxer.
-   Pete has no education past the ninth grade.
-   Roberta, the chef, and the police officer went golfing together.

Question: Who holds which jobs?

Data type for the jobs.

``` { .literate .haskell}
data Job  = Chef | Guard | Nurse | Clerk | PoliceOfficer | Teacher | Actor | Boxer
  deriving (Eq, Ord, Enum, Bounded, Show)
```

Data type for the people.

``` { .literate .haskell}
data Name = Roberta | Thelma | Steve | Pete
  deriving (Eq, Ord, Enum, Bounded, Show)
```

The list of all possible jobs.

``` { .literate .haskell}
jobs :: [Job]
jobs = listAll
```

The list of all possible people.

``` { .literate .haskell}
names :: [Name]
names = listAll
```

The actual solution is a relation that has exactly one value in every
column and exactly two values in every row. Additionally, some
properties are simpler to express in terms of rows, rather than a list
of negations.

``` { .literate .haskell}
solution :: Rel Name Job -> Rel Name Job
solution r | allRows rowPred r && allColumns colPred r = r where
  rowPred row = hasLength row 2 
                 && 
                 row `isNotEqual` [Chef, Clerk] 
                 && 
                 row `isNotEqual` [Chef, PoliceOfficer]
   
  colPred col = hasLength col 1
```

The preconditions specified by the puzzle.

``` { .literate .haskell}
preconditions :: Rel Name Job
preconditions = mkNonDetRel names jobs $
 [ 
   -- nurse is not female 
   Thelma  `isNot` Nurse, Roberta `isNot` Nurse
   -- Husband is clerk ==> clerk not female
 , Roberta `isNot` Clerk, Thelma  `isNot` Clerk
   -- Roberta is not the boxer
 , Roberta `isNot` Boxer
 -- Roberta is neither chef, nor police officer
 , Roberta `isNot` Chef,  Roberta `isNot` PoliceOfficer
 -- Pete is not the sharpest tool in the shed
 -- Meta: Smarts required by Teacher, Nurse, PoliceOfficer
 , Pete    `isNot` Nurse, Pete    `isNot` Teacher         , Pete `isNot` PoliceOfficer
 -- Meta: actor male
 , Thelma  `isNot` Actor, Roberta `isNot` Actor
 -- Meta: heterosexual marriage
 , Pete    `isNot` Chef,  Steve   `isNot` Chef
   ]
```

Solves the puzzle and returns all possible solutions.

``` { .literate .haskell}
solve :: IO ()
solve = values2list (set0 (solution preconditions)) >>= mapIO_ (putStrLn . showRel)
```
