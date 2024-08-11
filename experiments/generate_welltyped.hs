import Control.Monad.Except
import Data.Either
import Data.Foldable

arb_names :: [Name]
arb_names = (Name . List.singleton) `map` ['w' .. 'z']
arb_metas :: [Metavar]
arb_metas = Metavar `map` [0, 1]

instance Arbitrary Name where
  arbitrary = elements arb_names
instance Arbitrary Metavar where
  arbitrary = elements arb_metas

-- well-typed terms + contexts with types constructed from a set of base types
data WTTerm = WT Term ElabCtx
instance Arbitrary WTTerm where
  arbitrary = do
    ct <- arb_base_ctx
    (x, _) <- arb_tcd_tm ct
    pure $ WT x ct

arb_tcd_tm :: ElabCtx -> Gen (Term, Value)
arb_tcd_tm ctx = do
  -- we can generate random lambda abstractions just fine, but applications seem impossible
  -- when this gets "stuck" in the application case, it will loop trying to make well-typed apps
  n <- elements [0 .. 2]
  narr <- elements [0 .. n]
  arr <- sized_arb_arrow basetypes_ctx narr
  let rawtm = sized_arb_raw n
  let tm = flip (check ctx) arr <$> rawtm
  x <- tm `suchThat` (isRight . runExcept)
  pure (runTC_partial x, arr)

basetypes_ctx :: ElabCtx
basetypes_ctx = foldl define_const empty_ctx basetypes
  where
    basetypes :: [(Name, Value)]
    basetypes = [("Bool", VSort Star), ("Nat", VSort Star)]

-- assigns random meanings to all the arb_names and metavars
arb_base_ctx :: Gen ElabCtx
arb_base_ctx = do
  c <- foldlM arb_name_meaning basetypes_ctx arb_names
  foldlM arb_meta_meaning c arb_metas
  where
    arb_name_meaning :: ElabCtx -> Name -> Gen ElabCtx
    arb_name_meaning ct s = do
      coin <- arbitrary @Bool
      if coin
        then do
          (x, ty) <- arb_tcd_tm ct
          pure $ define_val ct (s, eval ct x, ty)
        else do
          ty <- sized $ sized_arb_arrow ct
          pure $ define_const ct (s, ty)
    arb_meta_meaning :: ElabCtx -> Metavar -> Gen ElabCtx
    arb_meta_meaning ct m = do
      ty <- sized $ sized_arb_arrow ct
      pure $ define_free ct (m, ty)

arb_basety :: ElabCtx -> Gen Value
arb_basety ctx = elements tys
  where
    tys = fmap (fst . snd) ct
    Ctx ct = ctx . toplvl

sized_arb_raw :: Int -> Gen Raw
sized_arb_raw 0 = elements $ RVar `map` arb_names <> RFree `map` arb_metas
sized_arb_raw i = do
  s <- arbitrary
  f <- sized_arb_raw (i `div` 2)
  x <- sized_arb_raw (i `div` 2)
  rest <- sized_arb_raw (i - 1)
  elements [f `RApp` x, RLam s rest]

sized_arb_arrow :: ElabCtx -> Int -> Gen Value
sized_arb_arrow ctx 0 = arb_basety ctx
sized_arb_arrow ctx i = do
  l <- arb_basety ctx
  r <- sized_arb_arrow ctx (i - 1)
  pure $ VPi "" l (const r)
