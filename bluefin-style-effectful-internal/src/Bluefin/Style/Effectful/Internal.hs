{-# LANGUAGE TypeFamilies #-}

module Bluefin.Style.Effectful.Internal where

import Control.Monad (when)
import Data.Foldable (for_)
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Effectful (Eff, runPureEff)
import qualified Effectful as Eff
import qualified Effectful.Dispatch.Dynamic as Dyn
import Effectful.Error.Static (Error)
import qualified Effectful.Error.Static as Eff
import Effectful.Fail (Fail)
import Effectful.State.Static.Local (State)
import qualified Effectful.State.Static.Local as Eff
import Prelude hiding (return)

class (a Eff.:> b) => a :> b

instance (e :> es) => e :> (x : es)

instance {-# INCOHERENT #-} e :> (e : es)

data Handle (eff :: k) (s :: k) where
  MkHandle :: (eff ~ s) => Handle eff s

to :: ((eff :> es) => t es r) -> (s :> es) => Handle eff s -> t es r
to = applyHandle

applyHandle :: ((eff :> es) => t es r) -> (s :> es) => Handle eff s -> t es r
applyHandle k h = case h of MkHandle -> k

withHandle :: (forall e. Handle eff e -> t (e : es) b) -> t (eff : es) b
withHandle k = k MkHandle

throwError :: (s :> es) => Handle (Error e) s -> e -> Eff es a
throwError h e = Eff.throwError e `applyHandle` h

withReturn ::
  (forall err. Handle (Error r) err -> Eff (err : effs) Void) ->
  Eff effs r
withReturn f = do
  r1 <- runErrorNoCallStack f
  pure $ case r1 of
    Right r -> absurd r
    Left l -> l

runErrorNoCallStack ::
  (forall s. Handle (Error e) s -> Eff (s : es) a) ->
  Eff es (Either e a)
runErrorNoCallStack k = Eff.runErrorNoCallStack $ withHandle k

get :: (s :> es) => Handle (State st) s -> Eff es st
get = (Eff.get `applyHandle`)

put :: (s :> es) => Handle (State st) s -> st -> Eff es ()
put h st = Eff.put st `applyHandle` h

evalState ::
  s ->
  (forall e. Handle (State s) e -> Eff (e : es) a) ->
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

twoState :: (Int, Int)
twoState = runPureEff $
  evalState 1 $ \s1 -> do
    evalState 2 $ \s2 -> do
      put s1 10
      put s2 20
      s1' <- get s1
      s2' <- get s2
      pure (s1', s2')

-- Direct encoding of the effects we want in our filesystem
data Filesystem m = MkFilesystem
  { readFileFS :: FilePath -> m String,
    writeFileFS :: FilePath -> String -> m ()
  }

-- A type class for such direct-style effects
class EffectDirect (e :: (Type -> Type) -> Type) where
  fmapEffect :: (forall a. m a -> n a) -> e m -> e n

-- Instance for the filesystem effect
instance EffectDirect Filesystem where
  fmapEffect f MkFilesystem {readFileFS = r, writeFileFS = w} =
    MkFilesystem {readFileFS = f . r, writeFileFS = \s -> f . w s}

-- Adapt direct effects for the existing cleff type-level encoding
data Direct f (m :: Type -> Type) (a :: Type) = Direct (f m -> m a)

type instance Eff.DispatchOf (Direct f) = Eff.Dynamic

-- Direct version of send
sendDirect ::
  Direct f :> es => (f (Eff es) -> Eff es a) -> Eff es a
sendDirect = Dyn.send . Direct

-- Define the effectful operations using sendDirect
readFile' ::
  (Direct Filesystem :> es) => FilePath -> Eff es String
readFile' x = sendDirect (\f -> readFileFS f x)

writeFile' ::
  (Direct Filesystem :> es) => FilePath -> String -> Eff es ()
writeFile' x y = sendDirect (\f -> writeFileFS f x y)

-- To run in IO, just define the effects directly
runFilesystemIO ::
  (Eff.IOE :> es) =>
  Eff (Direct Filesystem : es) a ->
  Eff es a
runFilesystemIO =
  interpretDirectIO
    MkFilesystem
      { readFileFS = readFile,
        writeFileFS = writeFile
      }

-- To run in State, just define the effects directly
filesystemToState ::
  (Fail :> es, State [(FilePath, String)] Eff.:> es) =>
  Eff (Direct Filesystem : es) a ->
  Eff es a
filesystemToState =
  interpretDirect
    MkFilesystem
      { readFileFS = \path ->
          Eff.gets (lookup path) >>= \case
            Nothing -> fail ("File not found: " ++ show path)
            Just contents -> pure contents,
        writeFileFS = \path contents ->
          Eff.modify ((path, contents) :)
      }

interpretDirectIO ::
  (Eff.IOE :> es, EffectDirect f) =>
  f IO ->
  Eff (Direct f : es) a ->
  Eff es a
interpretDirectIO = interpretDirect . fmapEffect Eff.liftIO

interpretDirect ::
  (EffectDirect f) =>
  f (Eff es) ->
  Eff (Direct f : es) a ->
  Eff es a
interpretDirect p = Dyn.interpret $ \env (Direct f) ->
  Dyn.localSeqUnlift env $ \k' ->
    Dyn.localSeqLift env $ \k ->
      k' (f (fmapEffect k p))
