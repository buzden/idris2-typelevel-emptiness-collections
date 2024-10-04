module Data.CheckedEmpty.List

import Data.Bool
import Data.List1
import Data.Vect
import Data.Zippable

import public Language.Implicits.IfUnsolved

%default total

--- Types definitions ---

public export
data Lst : (definitelyNotEmpty : Bool) -> Type -> Type where
  Nil  : Lst False a
  (::) : (0 _ : True `IfUnsolved` ine) => (0 _ : True `IfUnsolved` ne) =>
         a -> Lst ine a -> Lst ne a

%name Lst xs, ys, zs

||| An alias for a list that definitely may be empty.
||| Don't use this if you can be polymorphic on the boolean type argument.
public export %inline
Lst0 : Type -> Type
Lst0 = Lst False

public export %inline
Lst1 : Type -> Type
Lst1 = Lst True

--- Basic functions ---

public export
length : Lst ne a -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export %inline
(.length) : Lst ne a -> Nat
xs.length = length xs

public export
(++) : Lst nel a -> Lst ner a -> Lst (nel || ner) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: xs ++ ys

public export
Semigroup (Lst ne a) where
  xs <+> ys = rewrite sym $ orSameNeutral ne in xs ++ ys

public export
Monoid (Lst0 a) where
  neutral = []

public export
index' : (xs : Lst ne a) -> Fin xs.length -> a
index' (x::_ ) FZ     = x
index' (_::xs) (FS i) = index' xs i

public export %inline
index : Fin n -> (xs : Lst ne a) -> (0 _ : n = xs.length) => a
index i xs @{Refl} = index' xs i

--- Creation ---

public export
iterateN : (n : Nat) -> (a -> a) -> a -> Lst (n /= 0) a
iterateN Z     _ x = []
iterateN (S n) f x = x :: iterateN n f x

public export
tabulateN : (n : Nat) -> (Fin n -> a) -> Lst (n /= 0) a
tabulateN 0     _ = []
tabulateN (S k) f = f FZ :: tabulateN k (f . FS)

public export
replicate : (n : Nat) -> a -> Lst (n /= 0) a
replicate Z     _ = []
replicate (S k) x = x :: replicate k x

covering
public export
iterate : (a -> Maybe a) -> a -> Lst0 a
iterate f x = x :: case f x of
  Nothing => []
  Just y  => iterate f y

covering
public export
unfoldr : (b -> Maybe (a, b)) -> b -> Lst0 a
unfoldr f c = case f c of
  Nothing     => []
  Just (a, n) => a :: unfoldr f n

--- Internal conversions ---

-- Relaxation --

public export
relaxF : Lst ne a -> Lst0 a
relaxF []      = []
relaxF (x::xs) = x::xs

public export %inline
relaxT : Lst1 a -> Lst ne a
relaxT (x::xs) = x::xs

public export
relaxAnd : Lst ne a -> Lst (ne && nx) a
relaxAnd []      = []
relaxAnd (x::xs) = x::xs

%transform "relaxF=id"   relaxF   {ne} {a} = believe_me (\x => the (Lst ne a) x)
%transform "relaxT=id"   relaxT   {ne} {a} = believe_me (\x => the (Lst ne a) x)
%transform "relaxAnd=id" relaxAnd {ne} {a} = believe_me (\x => the (Lst ne a) x)

-- Strengthening --

public export
strengthen : Lst ne a -> Maybe $ Lst1 a
strengthen []      = Nothing
strengthen (x::xs) = Just $ x::xs

--- Functor ---

public export
Functor (Lst ne) where
  map f []      = []
  map f (x::xs) = f x :: map f xs

namespace NEHeteroOps

  public export
  bind : Lst nel a -> (a -> Lst ner b) -> Lst (nel && ner) b
  bind [] _ = []
  bind wh@(x::xs) f = do
    rewrite andCommutative nel ner
    let Just nxs = strengthen xs
      | Nothing => relaxAnd $ f x
    rewrite sym $ orSameNeutral ner
    relaxAnd $ f x ++ (assert_smaller wh nxs `bind` f)

  public export %inline
  bind' : Lst nel a -> Lst ner b -> Lst (nel && ner) b
  bind' xs ys = xs `bind` \_ => ys

  public export %inline
  join' : Lst nel (Lst ner a) -> Lst (nel && ner) a
  join' xs = xs `bind` id

  public export %inline
  ap : Lst nel (a -> b) -> Lst ner a -> Lst (nel && ner) b
  ap xs ys = xs `bind` (<$> ys)

public export %inline
Applicative (Lst ne) where
  pure x = [x]
  xs <*> ys = rewrite sym $ andSameNeutral ne in xs `ap` ys

public export %inline
Alternative Lst0 where
  empty = []
  xs <|> ys = xs ++ ys

public export %inline
Monad (Lst ne) where
  xs >>= f = rewrite sym $ andSameNeutral ne in xs `bind` f

--- Folds ---

public export
foldrLazy : (op : a -> Lazy b -> b) -> (init : Lazy b) -> Lst ne a -> b
foldrLazy _  init []      = init
foldrLazy op init (x::xs) = x `op` foldrLazy op init xs

public export
Foldable (Lst ne) where
  foldr c n []      = n
  foldr c n (x::xs) = c x (foldr c n xs)

  foldl f q []      = q
  foldl f q (x::xs) = foldl f (f q x) xs

  null []     = True
  null (_::_) = False

  toList []      = []
  toList (x::xs) = x :: toList xs

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

public export
foldl1 : (a -> a -> a) -> Lst1 a -> a
foldl1 f (x::xs) = foldl f x xs

public export
foldr1 : (op : a -> Lazy a -> a) -> Lst1 a -> a
foldr1 op [x]               = x
foldr1 op xyys@(x::(y::ys)) = op x $ foldr1 op $ assert_smaller xyys $ y::ys

public export
Traversable (Lst ne) where
  traverse f []      = pure []
  traverse f (x::xs) = [| f x :: traverse f xs |]

--- Reversing ---

public export
reverse : Lst ne a -> Lst ne a
reverse []      = []
reverse (x::xs) = foldl (flip (::)) [x] xs

--- Picking ---

public export
head : Lst1 a -> a
head (x::_) = x

public export
head' : Lst ne a -> Maybe a
head' = map head . strengthen

public export
tail : Lst1 a -> Lst0 a
tail (_::xs) = relaxF xs

public export
tail' : Lst ne a -> Maybe $ Lst0 a
tail' = map tail . strengthen

public export
last : Lst1 a -> a
last [x]     = x
last wh@(_::(y::ys)) = last $ assert_smaller wh $ y::ys

public export
last' : Lst ne a -> Maybe a
last' = map last . strengthen

public export
init : Lst1 a -> Lst0 a
init [x] = []
init wh@(x::(y::ys)) = x :: init (assert_smaller wh $ y::ys)

public export
init' : Lst ne a -> Maybe $ Lst0 a
init' = map init . strengthen

public export
unsnoc : Lst1 a -> (Lst0 a, a)
unsnoc = go [] where
  go : (rev : Lst0 a) -> Lst1 a -> (Lst0 a, a)
  go rev xxs@(x::xs) = case strengthen xs of
    Nothing  => (reverse rev, x)
    Just xs' => go (x::rev) $ assert_smaller xxs xs'

-- Returns the longest first
public export
tails : Lst ne a -> Lst1 $ Lst0 a
tails []          = [ [] ]
tails xxs@(x::xs) = relaxF xxs :: tails (assert_smaller xxs xs)

-- Returns the longest first
public export
tails1 : Lst ne a -> Lst ne $ Lst1 a
tails1 [] = []
tails1 xxs@(x::xs) = (x::xs) :: case strengthen xs of
  Nothing  => []
  Just xs' => relaxF $ tails1 $ assert_smaller xxs xs'

-- Returns the shortest first
public export
inits : Lst ne a -> Lst1 $ Lst0 a
inits []      = [ [] ]
inits (x::xs) = [] :: ((x::) <$> inits xs)

-- Returns the shortest first
public export
inits1 : Lst ne a -> Lst ne $ Lst1 a
inits1 []      = []
inits1 (x::xs) = [x] :: ((x::) <$> inits1 xs)

--- Sublisting ---

public export
take : (n : Nat) -> Lst ne a -> Lst (ne && n /= 0) a
take Z     _       = rewrite andFalseFalse ne in []
take _     []      = []
take (S k) (x::xs) = x :: take k xs

public export
drop : (n : Nat) -> Lst ne a -> Lst0 a
drop Z     xs      = relaxF xs
drop (S _) []      = []
drop (S n) (_::xs) = drop n $ relaxF xs

public export
takeWhile : (a -> Bool) -> Lst ne a -> Lst0 a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

public export
dropWhile : (a -> Bool) -> Lst ne a -> Lst0 a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

--- Zippings ---

public export
Zippable (Lst ne) where
  zipWith _ [] _ = []
  zipWith _ _ [] = []
  zipWith f xxs@((x::xs) @{_} @{ine}) (y::ys) =
    (f x y :: zipWith f (assert_smaller xxs $ relaxF xs) (relaxF ys)) @{%search} @{ine}

  zipWith3 _ [] _ _ = []
  zipWith3 _ _ [] _ = []
  zipWith3 _ _ _ [] = []
  zipWith3 f xxs@((x::xs) @{_} @{ine}) (y::ys) (z::zs) =
    (f x y z :: zipWith3 f (assert_smaller xxs $ relaxF xs) (relaxF ys) (relaxF zs)) @{%search} @{ine}

  unzipWith f [] = ([], [])
  unzipWith f (x::xs) = do
    let (y, z) = f x
    let (ys, zs) = unzipWith f xs
    (y::ys, z::zs)

  unzipWith3 f [] = ([], [], [])
  unzipWith3 f (x::xs) = do
    let (a, b, c) = f x
    let (as, bs, cs) = unzipWith3 f xs
    (a::as, b::bs, c::cs)

public export
zipWithStream : (a -> b -> c) -> Stream a -> Lst ne b -> Lst ne c
zipWithStream _ _       []      = []
zipWithStream f (x::xs) (y::ys) = f x y :: zipWithStream f xs ys

public export %inline
zipStream : Stream a -> Lst ne b -> Lst ne (a, b)
zipStream = zipWithStream (,)

--- Filtering ---

public export
filter : (a -> Bool) -> Lst ne a -> Lst0 a
filter _ []      = []
filter f (x::xs) = if f x then x :: filter f xs else filter f xs

public export
mapMaybe : (a -> Maybe b) -> Lst ne a -> Lst0 b
mapMaybe _ [] = []
mapMaybe f (x::xs) = case f x of
                       Just y  => y :: mapMaybe f xs
                       Nothing => mapMaybe f xs

--- External conversions ---

-- Foldable --

public export
fromFoldable : Foldable f => f a -> Lst0 a
fromFoldable = foldr (::) []

-- List --

public export
fromList : (xs : List a) -> Lst (not $ null xs) a
fromList []      = []
fromList (x::xs) = x :: fromList xs

public export
Cast (List a) (Lst0 a) where
  cast xs = relaxF $ fromList xs

-- List1 --

public export
fromList1 : List1 a -> Lst1 a
fromList1 $ x:::xs = x :: fromList xs

public export
toList1 : Lst1 a -> List1 a
toList1 $ x::xs = x ::: toList xs

public export
Cast (List1 a) (Lst True a) where
  cast = fromList1

public export
Cast (Lst True a) (List1 a) where
  cast = toList1

-- Vect --

public export
fromVect : Vect n a -> Lst (n /= Z) a
fromVect []      = []
fromVect (x::xs) = x :: fromVect xs

public export
Cast (Vect n a) (Lst (n /= Z) a) where
  cast = fromVect

--- Range syntax ---

public export %inline
rangeFromTo : Range a => a -> a -> Lst0 a
rangeFromTo l r = relaxF $ fromList $ rangeFromTo l r

public export %inline
rangeFromThenTo : Range a => a -> a -> a -> Lst0 a
rangeFromThenTo x y z = relaxF $ fromList $ rangeFromThenTo x y z

--- Showing ---

export
Show a => Show (Lst ne a) where
  show = show . toList

--- Properties ---

-- type itself, inhabitance --

export
{0 xs : Lst _ _} -> {0 uns0 : _} -> {0 uns1 : _} ->
Uninhabited ([] = (::) @{uns0} @{uns1} x xs) where
  uninhabited Refl impossible

export
{0 xs : Lst _ _} -> {0 uns0 : _} -> {0 uns1 : _} ->
Uninhabited ((::) @{uns0} @{uns1} x xs = []) where
  uninhabited Refl impossible

-- If either head or tail is not propositionally equal, conses are not propositionally equal
export
{0 xs : Lst _ _} ->
{0 unsL0 : _} -> {0 unsL1 : _} ->
{0 unsR0 : _} -> {0 unsR1 : _} ->
Either (Uninhabited $ x === y) (Uninhabited $ xs === ys) =>
Uninhabited ((::) @{unsL0} @{unsL1} x xs === (::) @{unsR0} @{unsR1} y ys) where
  uninhabited @{Left  z} Refl = uninhabited @{z} Refl
  uninhabited @{Right z} Refl = uninhabited @{z} Refl

-- type itself, constructors --

export
Biinjective CheckedEmpty.List.(::) where
  biinjective Refl = (Refl, Refl)

-- map --

export
mapFusion : (g : b -> c) -> (f : a -> b) -> (xs : Lst ne a) -> map g (map f xs) = map (g . f) xs
mapFusion g f []      = Refl
mapFusion g f (x::xs) = rewrite mapFusion g f xs in Refl

export
mapExt : (xs : Lst ne _) -> ((x : _) -> f x = g x) -> map f xs = map g xs
mapExt []      _  = Refl
mapExt (x::xs) fg = rewrite fg x in cong (g x ::) $ mapExt _ fg
