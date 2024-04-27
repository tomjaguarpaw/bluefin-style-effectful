{-# LANGUAGE TypeFamilies #-}

module Bluefin.Style.Effectful.Internal where

import Control.Monad (when)
import Data.Foldable (for_)
import Data.Kind (Constraint)
import Data.Void (Void, absurd)
import Effectful.Error.Static (Error)
import qualified Effectful.Error.Static as Eff
import Effectful.State.Static.Local (State)
import qualified Effectful.State.Static.Local as Eff
import Effectful (Eff, runPureEff)
import qualified Effectful as Eff
import Prelude hiding (return)

class (a Eff.:> b) => a :> b

instance (e :> es) => e :> (x : es)

instance {-# INCOHERENT #-} e :> (e : es)

data Dict c where
  Dict :: (c) => Dict c

data Has (eff :: k) (s :: k) where
  MkHas :: eff ~ s => Has eff s

type Handle = Has

mkHas :: Has a a
mkHas = mkHas

has :: (Has a a -> r) -> r
has f = f mkHas

{-# INLINE have #-}
have :: Has eff s -> Dict (eff ~ s)
have MkHas = Dict

to :: ((eff :> es) => t es r) -> (s :> es) => Has eff s -> t es r
to = applyHandle

applyHandle :: ((eff :> es) => t es r) -> (s :> es) => Handle eff s -> t es r
applyHandle k h = case have h of Dict -> k

from ::
  (t (eff : es) a -> t es b) ->
  (forall s. Has eff s -> t (s : es) a) ->
  t es b
from = withHandle'

withHandle' ::
  (t (eff : es) a -> t es b) ->
  (forall s. Handle eff s -> t (s : es) a) ->

  t es b
withHandle' f k = f (has k)

withHandle :: (forall e. Handle eff e -> t (e : es) b) -> t (eff : es) b
withHandle k = k mkHas

throwError :: (s :> es) => Has (Error e) s -> e -> Eff es a
throwError h e = Eff.throwError e `applyHandle` h

withReturn ::
  (forall err. Has (Error r) err -> Eff (err : effs) Void) ->
  Eff effs r
withReturn f = do
  r1 <- runErrorNoCallStack f
  pure $ case r1 of
    Right r -> absurd r
    Left l -> l

runErrorNoCallStack ::
  (forall s. Has (Error e) s -> Eff (s : es) a) ->
  Eff es (Either e a)
runErrorNoCallStack = from Eff.runErrorNoCallStack

get :: (s :> es) => Has (State st) s -> Eff es st
get = (Eff.get `applyHandle`)

put :: (s :> es) => Has (State st) s -> st -> Eff es ()
put h st = Eff.put st `applyHandle` h

evalState ::
  s ->
  (forall e. Has (State s) e -> Eff (e : es) a) ->
  Eff es a
evalState s k = Eff.evalState s $ withHandle k

(!?) :: [a] -> Int -> Maybe a
xs !? i = runPureEff $
  withReturn $ \return -> do
    evalState 0 $ \s -> do
      for_ xs $ \x -> do
        i' <- get s
        when (i == i') (throwError return (Just x))
        put s (i' + 1)
      throwError return Nothing

partial ::
  (st :> es, err :> es) =>
  [a] ->
  Int ->
  Has (Error (Maybe a)) err ->
  Has (State Int) st ->
  Eff es b
partial xs i return s = do
  for_ xs $ \x -> do
    i' <- get s
    when (i == i') (throwError return (Just x))
    put s (i' + 1)
  throwError return Nothing

data Compound e es where
  Compound ::
    (es ~ [st, err]) =>
    Has (Error e) err ->
    Has (State Int) st ->
    Compound e es

type family (ss :: [Eff.Effect]) ::> (es :: [Eff.Effect]) :: Constraint

type instance '[] ::> es = ()

type instance (s : ss) ::> es = (s :> es, ss ::> es)

type family (a :: [r]) +++ (b :: [r]) :: [r]

type instance '[] +++ rs = rs

type instance (a : as) +++ rs = a : (as +++ rs)

putC :: (ss ::> es) => Compound e ss -> Int -> Eff es ()
putC = \case Compound _ h -> put h

getC :: (ss ::> es) => Compound e ss -> Eff es Int
getC = \case Compound _ h -> get h

throwErrorC :: (ss ::> es) => Compound e ss -> e -> Eff es a
throwErrorC = \case Compound h _ -> throwError h

-- This leaks how many effects are inside.  I don't know how to do
-- better whilst still allowing type inference when doing
-- runEarlyReturnC of partialC.
runC ::
  Int ->
  (forall st err. Compound e '[st, err] -> Eff ('[st, err] +++ es) r) ->
  Eff es (Either e r)
runC st f =
  runErrorNoCallStack $ \e ->
    evalState st $ \s ->
      f (Compound e s)

runEarlyReturnC ::
  Int ->
  (forall st err. Compound r '[st, err] -> Eff ('[st, err] +++ es) r) ->
  Eff es r
runEarlyReturnC st f = fmap (either id id) (runC st f)

partialC ::
  (ss ::> es) =>
  [a] ->
  Int ->
  Compound (Maybe a) ss ->
  Eff es b
partialC xs i s = do
  for_ xs $ \x -> do
    i' <- getC s
    when (i == i') (throwErrorC s (Just x))
    putC s (i' + 1)
  throwErrorC s Nothing

(!??) :: [a] -> Int -> Maybe a
xs !?? i = runPureEff $
  withReturn $ \return -> do
    evalState 0 $ \s -> do
      partialC xs i (Compound return s)

(!???) :: [a] -> Int -> Maybe a
xs !??? i = runPureEff $
  runEarlyReturnC 0 $ \s -> do
    partialC xs i s

{-
def lookup(xs, i):
  try:
    s = 0
    for a in xs:
      i_ = s
      if (i == i_): return (Just a)
      s = i_ + 1
      return Nothing
-}

twoState :: (Int, Int)
twoState = runPureEff $
  evalState 1 $ \s1 -> do
    evalState 2 $ \s2 -> do
      put s1 10
      put s2 20
      s1' <- get s1
      s2' <- get s2
      pure (s1', s2')
