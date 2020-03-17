{-# LANGUAGE MultiParamTypeClasses, GeneralisedNewtypeDeriving, TypeApplications, OverloadedStrings #-}
module Main where

import Control.Arrow
import Control.Monad.Reader (MonadReader(ask,local),asks,ReaderT,runReaderT)
import GHC.Word (Word32)
import GHC.Arr (array)
import Simplicity.Ty.Bit (Bit, toBit)
import Simplicity.Ty.Word (Word256, word256, toWord, wordSize, fromWord1, fromWord)
import Simplicity.Programs.Word (fullAdder)
import Simplicity.Term.Core
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive (PrimEnv, primEnv)
import Simplicity.Digest (hash0)
import Data.Maybe (fromJust)

txoutput = TxOutput 1 "\x00"
outpoint = Outpoint {opHash=hash0, opIndex=(1 :: Word32)}
sigtxinput = SigTxInput {sigTxiPreviousOutpoint=outpoint, sigTxiValue=1, sigTxiSequence=1}
sigtxin = array (1,1) [(1,sigtxinput)]
sigtxout = array (1,1) [(1,txoutput)]
sigtx = SigTx 2 sigtxin sigtxout 1
primenv = fromJust $ primEnv sigtx 1 hash0

newtype MyMonad a = MyMonad { runMyMonad :: ReaderT PrimEnv IO a }
    deriving (Functor, Applicative, Monad)

instance MonadReader PrimEnv MyMonad where
    ask = MyMonad ask
    local f = id

instance MonadFail MyMonad where
    fail = error

type WT = Word256
wtyp = word256

{-# RULES
    "fullAdderOpt" forall w. fullAdder w = Kleisli (\((a,b),c) -> (return :: a -> MyMonad a) $ let sum = fromWord w a + fromWord w b + fromWord1 c in (toBit (sum >= 2 ^ wordSize w), toWord w sum))
  #-}

primcalc :: MyMonad WT
primcalc = do
  let (x,y) = (toWord wtyp 1,toWord wtyp 2)
  (bit, (a,b)) <- runKleisli (fullAdder wtyp ) ((x, y), toBit False)
  return (a, b)

main :: IO ()
main = do
  (o1, o2) <- (runReaderT $ runMyMonad $ primcalc) primenv
  print o1
  print o2
  pure ()
