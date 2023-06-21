module Data.CheckedEmpty.List.Lazy

import Control.Function

import Data.Bool
import Data.List.Lazy
import Data.Fin
import Data.Zippable

import public Language.Implicits.IfUnsolved

%default total

--- Types definitions ---

public export
data LazyLst : (definitelyNotEmpty : Bool) -> Type -> Type where
  Nil  : LazyLst False a
  (::) : (0 _ : True `IfUnsolved` ine) => (0 _ : True `IfUnsolved` ne) =>
         a -> Lazy (LazyLst ine a) -> LazyLst ne a

%name LazyLst xs, ys, zs

||| An alias for a list that definitely may be empty.
||| Don't use this if you can be polymorphic on the boolean type argument.
public export %inline
LazyLst0 : Type -> Type
LazyLst0 = LazyLst False

public export %inline
LazyLst1 : Type -> Type
LazyLst1 = LazyLst True

--- Basic functions ---

public export
length : LazyLst ne a -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export %inline
(.length) : LazyLst ne a -> Nat
xs.length = length xs

public export
(++) : LazyLst nel a -> Lazy (LazyLst ner a) -> LazyLst (nel || ner) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: xs ++ ys

public export
Semigroup (LazyLst ne a) where
  xs <+> ys = rewrite sym $ orSameNeutral ne in xs ++ ys

public export
Monoid (LazyLst0 a) where
  neutral = []

public export
index' : (xs : LazyLst ne a) -> Fin xs.length -> a
index' (x::_ ) FZ     = x
index' (_::xs) (FS i) = index' xs i

public export %inline
index : Fin n -> (xs : LazyLst ne a) -> (0 _ : n = xs.length) => a
index i xs @{Refl} = index' xs i

--- Creation ---

public export
iterateN : (n : Nat) -> (a -> a) -> a -> LazyLst (n /= 0) a
iterateN Z     _ x = []
iterateN (S n) f x = x :: iterateN n f (f x)

public export
tabulateN : (n : Nat) -> (Fin n -> a) -> LazyLst (n /= 0) a
tabulateN 0     _ = []
tabulateN (S k) f = f FZ :: tabulateN k (f . FS)

public export
replicate : (n : Nat) -> a -> LazyLst (n /= 0) a
replicate Z     _ = []
replicate (S k) x = x :: replicate k x

covering
public export
iterate : (a -> Maybe a) -> a -> LazyLst0 a
iterate f x = x :: case f x of
  Nothing => []
  Just y  => iterate f y

covering
public export
unfoldr : (b -> Maybe (a, b)) -> b -> LazyLst0 a
unfoldr f c = case f c of
  Nothing     => []
  Just (a, n) => a :: unfoldr f n

--- Internal conversions ---

-- Relaxation --

public export
relaxF : LazyLst ne a -> LazyLst0 a
relaxF []      = []
relaxF (x::xs) = x::xs

public export %inline
relaxT : LazyLst1 a -> LazyLst ne a
relaxT (x::xs) = x::xs

public export
relaxAnd : LazyLst ne a -> LazyLst (ne && nx) a
relaxAnd []      = []
relaxAnd (x::xs) = x::xs

%transform "relaxF=id"   relaxF   {ne} {a} = believe_me (\x => the (LazyLst ne a) x)
%transform "relaxT=id"   relaxT   {ne} {a} = believe_me (\x => the (LazyLst ne a) x)
%transform "relaxAnd=id" relaxAnd {ne} {a} = believe_me (\x => the (LazyLst ne a) x)

-- Strengthening --

public export
strengthen : LazyLst ne a -> Maybe $ LazyLst1 a
strengthen []      = Nothing
strengthen (x::xs) = Just $ x::xs

--- Functor ---

public export
Functor (LazyLst ne) where
  map f []      = []
  map f (x::xs) = f x :: map f xs

namespace NEHeteroOps

  export
  bind : LazyLst nel a -> (a -> LazyLst ner b) -> LazyLst (nel && ner) b
  bind [] _ = []
  bind wh@(x::xs) f = do
    rewrite andCommutative nel ner
    let Just nxs = strengthen xs
      | Nothing => relaxAnd $ f x
    rewrite sym $ orSameNeutral ner
    relaxAnd $ f x ++ (assert_smaller wh nxs `bind` f)

  export %inline
  bind' : LazyLst nel a -> LazyLst ner b -> LazyLst (nel && ner) b
  bind' xs ys = xs `bind` \_ => ys

  export %inline
  join' : LazyLst nel (LazyLst ner a) -> LazyLst (nel && ner) a
  join' xs = xs `bind` id

  export %inline
  ap : LazyLst nel (a -> b) -> LazyLst ner a -> LazyLst (nel && ner) b
  ap xs ys = xs `bind` (<$> ys)

public export %inline
Applicative (LazyLst ne) where
  pure x = [x]
  xs <*> ys = rewrite sym $ andSameNeutral ne in xs `ap` ys

public export %inline
Alternative LazyLst0 where
  empty = []
  (<|>) = (++)

public export %inline
Monad (LazyLst ne) where
  xs >>= f = rewrite sym $ andSameNeutral ne in xs `bind` f

--- Folds ---

public export
foldrLazy : (op : a -> Lazy b -> b) -> (init : Lazy b) -> LazyLst ne a -> b
foldrLazy _  init []      = init
foldrLazy op init (x::xs) = x `op` foldrLazy op init xs

export
Foldable (LazyLst ne) where
  foldr c n []      = n
  foldr c n (x::xs) = c x (foldr c n xs)

  foldl f q []      = q
  foldl f q (x::xs) = foldl f (f q x) xs

  null []     = True
  null (_::_) = False

  foldlM op init []      = pure init
  foldlM op init (x::xs) = op init x >>= \next => foldlM op next xs

  toList []      = []
  toList (x::xs) = x :: toList xs

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

export
foldl1 : (a -> a -> a) -> LazyLst1 a -> a
foldl1 f (x::xs) = foldl f x xs

export
foldr1 : (a -> Lazy a -> a) -> LazyLst1 a -> a
foldr1 op [x] = x
foldr1 op (x::xs@(y::ys)) = op x $ foldr1 op $ assert_smaller xs (y::ys)

public export
traverse_ : Monad m => (a -> m b) -> LazyLst ne a -> m Unit
traverse_ f = foldrLazy ((>>) . ignore . f) (pure ())

public export %inline
for_ : Monad m => LazyLst ne a -> (a -> m b) -> m Unit
for_ = flip Lazy.traverse_

public export %inline
sequence_ : Monad m => LazyLst ne (m a) -> m Unit
sequence_ = Lazy.traverse_ id

--- Picking ---

public export
head : LazyLst1 a -> a
head (x::_) = x

public export
head' : LazyLst ne a -> Maybe a
head' = map head . strengthen

public export
tail : LazyLst1 a -> LazyLst0 a
tail (_::xs) = relaxF xs

public export
tail' : LazyLst ne a -> Maybe $ LazyLst0 a
tail' = map tail . strengthen

public export
last : LazyLst1 a -> a
last [x]     = x
last wh@(_::(y::ys)) = last $ assert_smaller wh $ y::ys

public export
last' : LazyLst ne a -> Maybe a
last' = map last . strengthen

public export
init : LazyLst1 a -> LazyLst0 a
init [x] = []
init wh@(x::(y::ys)) = x :: init (assert_smaller wh $ y::ys)

public export
init' : LazyLst ne a -> Maybe $ LazyLst0 a
init' = map init . strengthen

-- Returns the longest first
public export
tails : LazyLst ne a -> LazyLst1 $ LazyLst0 a
tails []          = [ [] ]
tails xxs@(x::xs) = relaxF xxs :: tails (assert_smaller xxs xs)

-- Returns the longest first
public export
tails1 : LazyLst ne a -> LazyLst ne $ LazyLst1 a
tails1 [] = []
tails1 xxs@(x::xs) = (x::xs) :: case strengthen xs of
  Nothing  => []
  Just xs' => relaxF $ tails1 $ assert_smaller xxs xs'

-- Returns the shortest first
public export
inits : LazyLst ne a -> LazyLst1 $ LazyLst0 a
inits []      = [ [] ]
inits (x::xs) = [] :: ((x::) <$> inits xs)

-- Returns the shortest first
public export
inits1 : LazyLst ne a -> LazyLst ne $ LazyLst1 a
inits1 []      = []
inits1 (x::xs) = [x] :: ((x::) <$> inits1 xs)

--- Sublisting ---

public export
take : (n : Nat) -> LazyLst ne a -> LazyLst (ne && n /= 0) a
take Z     _       = rewrite andFalseFalse ne in []
take _     []      = []
take (S k) (x::xs) = x :: take k xs

public export
drop : (n : Nat) -> LazyLst ne a -> LazyLst0 a
drop Z     xs      = relaxF xs
drop (S _) []      = []
drop (S n) (_::xs) = drop n $ relaxF xs

public export
takeWhile : (a -> Bool) -> LazyLst ne a -> LazyLst0 a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

public export
dropWhile : (a -> Bool) -> LazyLst ne a -> LazyLst0 a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

--- Zippings ---

export
Zippable (LazyLst ne) where
  zipWith _ [] _ = []
  zipWith _ _ [] = []
  zipWith f xxs@((x::xs) @{_} @{ine}) (y::ys) = (f x y :: zipWith f (assert_smaller xxs $ relaxF xs) (relaxF ys)) @{%search} @{ine}

  zipWith3 _ [] _ _ = []
  zipWith3 _ _ [] _ = []
  zipWith3 _ _ _ [] = []
  zipWith3 f xxs@((x::xs) @{_} @{ine}) (y::ys) (z::zs) = (f x y z :: zipWith3 f (assert_smaller xxs $ relaxF xs) (relaxF ys) (relaxF zs)) @{%search} @{ine}

  unzipWith  f xs = (xs <&> fst . f, xs <&> snd . f)
  unzipWith3 f xs = (xs <&> fst . f, xs <&> fst . snd . f, xs <&> snd . snd . f)

export
zipWithStream : (a -> b -> c) -> Stream a -> LazyLst ne b -> LazyLst ne c
zipWithStream _ _       []      = []
zipWithStream f (x::xs) (y::ys) = f x y :: zipWithStream f xs ys

export %inline
zipStream : Stream a -> LazyLst ne b -> LazyLst ne (a, b)
zipStream = zipWithStream (,)

--- Filtering ---

export
filter : (a -> Bool) -> LazyLst ne a -> LazyLst0 a
filter _ []      = []
filter f (x::xs) = if f x then x :: filter f xs else filter f xs

export
mapMaybe : (a -> Maybe b) -> LazyLst ne a -> LazyLst0 b
mapMaybe _ [] = []
mapMaybe f (x::xs) = case f x of
                       Just y  => y :: mapMaybe f xs
                       Nothing => mapMaybe f xs

--- External conversions ---

-- Foldable --

public export
fromFoldable : Foldable f => f a -> LazyLst0 a
fromFoldable = foldr (\x, xs => x :: xs) []

-- List --

public export
fromList : (xs : List a) -> LazyLst (not $ null xs) a
fromList []      = []
fromList (x::xs) = x :: fromList xs

public export
Cast (List a) (LazyLst0 a) where
  cast xs = relaxF $ fromList xs

-- LazyList --

public export
fromLazyList : (xs : LazyList a) -> LazyLst (not $ null xs) a
fromLazyList []      = []
fromLazyList (x::xs) = x :: fromLazyList xs

public export
Cast (LazyList a) (LazyLst0 a) where
  cast xs = relaxF $ fromLazyList xs

public export
toLazyList : LazyLst ne a -> LazyList a
toLazyList []      = []
toLazyList (x::xs) = x :: toLazyList xs

public export
Cast (LazyLst ne a) (LazyList a) where
  cast = toLazyList

-- Stream --

covering
public export
fromStream : Stream a -> LazyLst1 a
fromStream $ x::xs = x :: fromStream xs

--- Range syntax ---

-- not really lazy in its nature
public export %inline
rangeFromTo : Range a => a -> a -> LazyLst0 a
rangeFromTo l r = relaxF $ fromList $ rangeFromTo l r

-- not really lazy in its nature
public export %inline
rangeFromThenTo : Range a => a -> a -> a -> LazyLst0 a
rangeFromThenTo x y z = relaxF $ fromList $ rangeFromThenTo x y z

covering
public export %inline
rangeFrom : Range a => (0 _ : IfUnsolved ne True) => a -> LazyLst ne a
rangeFrom = relaxT . fromStream . rangeFrom

covering
public export %inline
rangeFromThen : Range a => (0 _ : IfUnsolved ne True) => a -> a -> LazyLst ne a
rangeFromThen = relaxT .: fromStream .: rangeFromThen

--- Showing ---

export
Show a => Show (LazyLst ne a) where
  show = show . toList

export
[DoNotEval] Show a => Show (LazyLst ne a) where
  show []     = "[]"
  show (x::_) = "\{show x} :: <lazy>"

--- Properties ---

-- type itself, inhabitance --

export
{0 xs : LazyLst _ _} -> {0 uns0 : _} -> {0 uns1 : _} ->
Uninhabited ([] = (::) @{uns0} @{uns1} x xs) where
  uninhabited Refl impossible

export
{0 xs : LazyLst _ _} -> {0 uns0 : _} -> {0 uns1 : _} ->
Uninhabited ((::) @{uns0} @{uns1} x xs = []) where
  uninhabited Refl impossible

-- If either head or tail is not propositionally equal, conses are not propositionally equal
export
{0 xs : LazyLst _ _} ->
{0 unsL0 : _} -> {0 unsL1 : _} ->
{0 unsR0 : _} -> {0 unsR1 : _} ->
Either (Uninhabited $ x === y) (Uninhabited $ xs === ys) =>
Uninhabited ((::) @{unsL0} @{unsL1} x xs === (::) @{unsR0} @{unsR1} y ys) where
  uninhabited @{Left  z} Refl = uninhabited @{z} Refl
  uninhabited @{Right z} Refl = uninhabited @{z} Refl

-- type itself, constructors --

Biinjective (with CheckedEmpty.List.Lazy.(::) \x, y => x :: y) where
  biinjective Refl = (Refl, Refl)

export
mapFusion : (g : b -> c) -> (f : a -> b) -> (xs : LazyLst ne a) -> map g (map f xs) = map (g . f) xs
mapFusion g f []      = Refl
mapFusion g f (x::xs) = rewrite mapFusion g f xs in Refl

export
mapExt : (xs : LazyLst ne _) -> ((x : _) -> f x = g x) -> map f xs = map g xs
mapExt []      _  = Refl
mapExt (x::xs) fg = rewrite fg x in cong (g x ::) $ mapExt _ fg
