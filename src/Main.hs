{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}

module Main where

import Reflex
import Reflex.Dom
import Control.Comonad.Cofree
import Data.Functor.Compose
import Control.Comonad
import Text.Read
import Data.Maybe
import Data.Foldable
import Control.Monad.Fix
import Control.Comonad.Trans.Cofree (CofreeT(..))
import qualified Control.Comonad.Trans.Cofree as CT
import qualified Data.Map as Map

main :: IO ()
main = mainWidget $ do
  el "h1" $ text "Hello Reflex!"
  -- renderFixedWidget $ fixWidgetDynamicNew widgetFunctor2
  _ <- getDynamicM
     $ cofreeCataT (\_ _ -> DynamicM $ text "YO!" >> return (constDyn ()))
     $ memoExtendCofreeT
         (\_ fi -> let r = sizeOfAst fi
                    in DynamicM $ do
                         el "div" $ text $ "SIZE: " ++ show r
                         return (constDyn r)
         )
     $ fixToCofreeT
     $ altFixDyn widgetFunctor2
  return ()

newtype DynamicM t m a = DynamicM { getDynamicM :: m (Dynamic t a) }

instance (MonadHold t m, Reflex t) => Functor (DynamicM t m) where
  fmap f (DynamicM m) = DynamicM $ mapDyn f =<< m

instance (MonadHold t m, Reflex t) => Applicative (DynamicM t m) where
  pure = DynamicM . return . constDyn
  DynamicM mf <*> DynamicM ma = DynamicM $ do
    df <- mf
    da <- ma
    dboth <- combineDyn (,) df da
    mapDyn (\(f,a) -> f a) dboth

instance (MonadWidget t m, Reflex t) => Monad (DynamicM t m) where
  return = pure
  a >>= f = theJoin (fmap f a)
    where
    theJoin (DynamicM a) = DynamicM $ do
      d <- a >>= mapDyn getDynamicM
      d' <- widgetDyn d
      return (joinDyn d')

data Ast a
  = ALambda String a
  | AApply a a
  | ANumber Int
  | AString String
  | AIdent String
  deriving (Functor, Foldable, Traversable)

sizeOfAst :: Ast Int -> Int
sizeOfAst x = case x of
  ANumber _ -> 2
  AString _ -> 2
  AIdent _ -> 2
  AApply a b -> 1 + a + b
  ALambda _ a -> 2 + a

data AstCons = CLambda | CApply | CNumber | CString | CIdent
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

allAstCons :: [AstCons]
allAstCons = [minBound..maxBound]

widgetFunctor :: MonadWidget t m
  => Compose m (Dynamic t) a
  -> Compose (Compose m (Dynamic t)) Ast a
widgetFunctor (Compose x) = Compose . Compose $ do
  d1 <- dropdown CNumber (constDyn $ Map.fromList $ flip map allAstCons $ \a -> (a, show a)) def
  let dynAstCons = _dropdown_value d1
  fmap joinDyn $ (widgetDyn =<<) $ forDyn dynAstCons $ \a -> case a of
    CNumber -> do
      text "Number "
      t1 <- textInput def
      dynNum <- foldDynMaybe (\str _ -> readMaybe str) 0
                             (_textInput_input t1)
      mapDyn ANumber dynNum
    CApply -> do
      text "Function "
      dynFunc <- x
      text "Value "
      dynVal <- x
      combineDyn AApply dynFunc dynVal
    _ -> error "write this case"

listItem, unorderedList :: String
listItem = "li"
unorderedList = "ul"

widgetFunctor2 :: MonadWidget t m
  => m (Dynamic t a)
  -> m (Dynamic t (Ast a))
widgetFunctor2 x = do
  d1 <- dropdown CNumber (constDyn $ Map.fromList $ flip map allAstCons $ \a -> (a, show a)) def
  let dynAstCons = _dropdown_value d1
  el unorderedList $ fmap joinDyn $ (widgetDyn =<<) $ forDyn dynAstCons $ \a -> case a of
    CNumber -> el listItem $ do
      text "Number "
      t1 <- textInput def
      dynNum <- foldDynMaybe (\str _ -> readMaybe str) 0 (_textInput_input t1)
      mapDyn ANumber dynNum
    CIdent -> el listItem $ do
      text "Identifier "
      mapDyn AIdent =<< fmap _textInput_value (textInput def)
    CString -> el listItem $ do
      text "String "
      mapDyn AString =<< fmap _textInput_value (textInput def)
    CApply -> do
      dynFunc <- el listItem $ do
        text "Function "
        x
      dynVal <- el listItem $ do
        text "Value "
        x
      combineDyn AApply dynFunc dynVal
    CLambda -> do
      dynVar <- el listItem $ do
        text "Variable Binding "
        fmap _textInput_value $ textInput def
      dynBody <- el listItem $ do
        text "Body "
        x
      combineDyn ALambda dynVar dynBody

altFixDyn :: (MonadWidget t m, Functor f)
  => (forall a. m (Dynamic t a) -> m (Dynamic t (f a)))
  -> Fix (Compose (DynamicM t m) f)
altFixDyn f = id
  $ Fix $ Compose
  $ (fmap . fmap) mkFixWidget2
  $ DynamicM
  $ f (getDynamicM $ getCompose $ unFix $ altFixDyn f)

mkFixWidget2 :: (MonadWidget t m, Functor f)
  => f (Fix (Compose (DynamicM t m) f))
  -> Fix (Compose (DynamicM t m) f)
mkFixWidget2 = Fix . Compose . DynamicM . return . constDyn

widgetDyn :: MonadWidget t m => Dynamic t (m a) -> m (Dynamic t a)
widgetDyn d = do
  widgetInit <- sample (current d)
  widgetHold widgetInit (updated d)

-- | memoExtend is similar to the comonadic extend except that each
--   node can only look at:
--
--   1. Its own current annotation
--   2. Its children's new annotations
--
--   This means that it does not have to reevaluate the entire
--   tree each time it calculates the new annotation for a node.
memoExtend :: Functor f => (b -> f a -> a) -> Cofree f b -> Cofree f a
memoExtend f (b :< cs) =
  let fca = fmap (memoExtend f) cs
   in f b (fmap extract fca) :< fca

memoExtendCofreeT :: (Monad w, Traversable f)
  => (b -> f a -> w a) -> CofreeT f w b -> CofreeT f w a
memoExtendCofreeT f (CofreeT w) = CofreeT $ do
  b CT.:< fctb <- w
  fcf <- traverse (runCofreeT . memoExtendCofreeT f) fctb
  let fa = fmap (\(a CT.:< fb) -> a) fcf
  a <- f b fa
  return (a CT.:< fmap (CofreeT . return) fcf)

fixToCofree :: Functor f => Fix f -> Cofree f ()
fixToCofree (Fix f) = () :< fmap fixToCofree f

fixToCofreeT :: (Functor f, Functor w) => Fix (Compose w f) -> CofreeT f w ()
fixToCofreeT (Fix (Compose w)) =
  CofreeT (fmap (\f -> () CT.:< fmap fixToCofreeT f) w)

newtype Fix f = Fix { unFix :: f (Fix f) }

cofreeCataT :: (Traversable f, Monad w) => (b -> f a -> w a) -> CofreeT f w b -> w a
cofreeCataT f (CofreeT x) = do
  b CT.:< fct <- x
  fa <- traverse (cofreeCataT f) fct
  f b fa

-- ana       :: Functor f => (a ->     f a)  -> a -> Fix    f
-- ana       f x = Fix        $ fmap (ana       f) $ f x
--
-- cofreeAna :: Functor f => (b -> (a, f b)) -> b -> Cofree f a
-- cofreeAna f x = (fst y :<) $ fmap (cofreeAna f) $ snd y where y = f x

-- cata       :: Functor f => (     f a -> a) -> Fix    f   -> a
-- cata       f x = f             $ fmap (cata       f) $ unFix  x
--
-- cofreeCata :: Functor f => (b -> f a -> a) -> Cofree f b -> a
-- cofreeCata f x = f (extract x) $ fmap (cofreeCata f) $ unwrap x

-- theWidgetFixed :: MonadWidget t m => Fix (Compose (Compose m (Dynamic t)) Ast)
-- theWidgetFixed = ana
--   (Compose . Compose . widgetFunctor3)
--   (error "dont use this")

-- instance (MonadWidget t m, Reflex t) => MonadFix (DynamicM t m) where
--   mfix f = do
--     <- mfix (getDynamicM . f)
--     DynamicM (mfix (getDynamicM . f))

-- data MyType = MyInt Int | MyString String
--
-- data Result
--   = ResultTypeError
--   | ResultNeeds

-- g a -> g (f a)
-- g (Fix (Compose g f)) -> g (f (Fix (Compose g f)))
--
-- What I want:
-- Fix (Compose g f)

--
-- widgetCofree :: MonadWidget t m
--   => Cofree f a -> Cofree (Compose (Compose (Dynamic t) m) f) a
-- widgetCofree = hoistCofree


-- widgetCofree :: MonadWidget t m => (f () -> m ()) -> Cofree f () -> Cofree _ (m ())
--
-- originalHoistCofree :: Functor f => (forall x . f x -> g x) -> Cofree f a -> Cofree g a
-- originalHoistCofree f (x :< y) = x :< f (originalHoistCofree f <$> y)
--
-- altHoistCofree :: Functor f => (forall h. f (Cofree h a) -> g (Cofree h a)) -> Cofree f a -> Cofree g a
-- altHoistCofree f (x :< y) = x :< f (altHoistCofree f <$> y)
--
-- altHoistCofree2 :: Functor f => (f (Cofree g a) -> g (Cofree g a)) -> Cofree f a -> Cofree g a
-- altHoistCofree2 f (x :< y) = x :< f (altHoistCofree2 f <$> y)

-- case x of
-- AIdent str ->
-- return . constDyn

-- memoExtendCofreeT :: (Monad w, MonadFix w, Traversable f) => (b -> f a -> w a) -> CofreeT f w b -> CofreeT f w a
-- memoExtendCofreeT f (CofreeT w) = CofreeT $ do
--   rec a <- f b fa
--       b CT.:< fctb <- w
--       fcf <- traverse (runCofreeT . memoExtendCofreeT f) fctb
--       let fa = fmap (\(a CT.:< fb) -> a) fcf
--   return (a CT.:< fmap (CofreeT . return) fcf)

-- memoExtendCofreeT :: (Monad w, Traversable f) => (b -> f a -> w a) -> CofreeT f w b -> CofreeT f w a
-- memoExtendCofreeT f (CofreeT w) = CofreeT $ do
--   b CT.:< fctb <- w
--   fcf <- for fctb $ \(CofreeT x) -> do
--     fcx
--     (runCofreeT . memoExtendCofreeT f) fctb
--   let fa = fmap (\(a CT.:< fb) -> a) fcf
--   a <- f b fa
--   return (a CT.:< fmap (CofreeT . return) fcf)

--
-- fixWidgetDynamic :: MonadWidget t m
--   => (m (Dynamic t (Fix f)) -> m (Dynamic t (f (Fix f))))
--   -> m (Dynamic t (Fix f))
-- fixWidgetDynamic f = do
--   d <- f (fixWidgetDynamic f)
--   mapDyn Fix d
--
-- fixWidgetDynamicNew :: (MonadWidget t m, Functor f)
--   => (forall a. m (Dynamic t a) -> m (Dynamic t (f a)))
--   -> Fix (Compose (Compose m (Dynamic t)) f)
-- fixWidgetDynamicNew f = id
--   $ Fix $ Compose $ Compose
--   $ (fmap . fmap . fmap) mkFixWidget
--   $ f (getCompose $ getCompose $ unFix $ fixWidgetDynamicNew f)
--
-- instance Reflex t => Functor (Dynamic t) where
--   fmap f d = unsafeDynamic (fmap f $ current d) (fmap f $ updated d)

-- mapFix :: (forall a. f a -> g a) -> Fix f -> Fix g
-- mapFix f (Fix a) = Fix (fmap (mapFix f) a)

-- renderFixedWidget :: (Functor f, MonadWidget t m)
--   => Fix (Compose (Compose m (Dynamic t)) f)
--   -> m ()
-- renderFixedWidget = cata $ \(Compose (Compose mdynf)) -> mdynf >> return ()

-- renderWidget :: (MonadWidget t m, Foldable f)
--   => Compose (Compose m (Dynamic t)) f (m ())
--   -> m ()
-- renderWidget (Compose (Compose m)) = do
--   d <- m
--   widgetDyn =<< mapDyn sequenceA_ d
--   return ()

-- mkFixWidget :: (MonadWidget t m, Functor f)
--   => f (Fix (Compose (Compose m (Dynamic t)) f))
--   -> Fix (Compose (Compose m (Dynamic t)) f)
-- mkFixWidget = Fix . Compose . Compose . return . constDyn

