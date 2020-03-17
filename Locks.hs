{-# LANGUAGE MultiParamTypeClasses, GeneralisedNewtypeDeriving, TypeApplications, OverloadedStrings #-}
module Main where

import Control.Arrow
import Control.Monad.Reader (MonadReader(ask,local),asks,ReaderT,runReaderT)
import qualified GHC.Word (Word32)
import GHC.Arr (array)
import Simplicity.Ty.Bit (Bit, toBit)
import Simplicity.Ty.Word
import Simplicity.Programs.Word (fullAdder)
import Simplicity.Term.Core
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive (Prim(..), PrimEnv, primSem, primEnv)
import Simplicity.Bitcoin.Term (primitive)
import Simplicity.Digest (hash0)
import Data.Maybe (fromJust)

txoutput = TxOutput 1 "\x00"
outpoint = Outpoint {opHash=hash0, opIndex=(1 :: GHC.Word.Word32)}
sigtxin = array
              (1,2) -- start bound, end bound, inclusive
              [(1,SigTxInput {sigTxiPreviousOutpoint=outpoint, sigTxiValue=1, sigTxiSequence=2})  -- [(index, value)]
              ,(2,SigTxInput {sigTxiPreviousOutpoint=outpoint, sigTxiValue=1, sigTxiSequence=8})]
sigtxout = array (1,1) [(1,txoutput)]
sigtx = SigTx { sigTxVersion = 2, sigTxIn = sigtxin, sigTxOut = sigtxout, sigTxLock = 4}
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

primcalc :: MyMonad (Word32, Either () Word32, Word32)
primcalc = do
  let inputIndex = (toWord word32 2)
  env <- ask
  a <- runKleisli (primitive CurrentSequence) ()
  b <- runKleisli (primitive InputSequence) inputIndex
  c <- runKleisli (primitive LockTime) ()
  return (a, b, c)

main :: IO ()
main = do
  (o1, o2, o3) <- (runReaderT $ runMyMonad $ primcalc) primenv
  print o1
  print o2
  print o3
  pure ()
