{-# LANGUAGE StandaloneDeriving, TypeApplications, PartialTypeSignatures, FlexibleInstances, MultiParamTypeClasses #-}
module Main where

import Prelude hiding (drop, replicate)
import Data.Maybe (fromJust)
import Data.Either (fromRight)
import Data.ByteString (replicate)
import Simplicity.MerkleRoot (commitmentRoot, CommitmentRoot)
import Simplicity.Bitcoin.Term (Primitive)
import Simplicity.Programs.Bit (cond, Bit)
import Simplicity.Programs.Generic (scribe) -- eq
import Simplicity.Term.Core ((>>>), drop, unit, assertl, Witness, Assert, TyC)
import Simplicity.Ty.Word (Vector64)
import Simplicity.Bitcoin.Programs.CheckSigHashAll hiding (XOnlyPubKey, Sig)
import Data.Serialize (decode)
import CheckSigNoInput (privateToPublic)
import Crypto.Secp256k1 (SecKey, secKey)
import Control.Arrow (Kleisli(Kleisli))
import Data.Functor.Identity (Identity(Identity))
import Control.Monad.Reader (MonadReader(ask,local),asks,ReaderT,runReaderT)
import Simplicity.Bitcoin.Primitive (Prim(..), PrimEnv, primEnv, envTx)

childToKey :: SecKey
childToKey = fromJust $ secKey $ replicate 32 32

v :: Vector64 Bit
v = fromRight (error "no go") $ Data.Serialize.decode $ replicate 64 64

ha :: Hash
ha = ((v, v), (v, v))

oldfashioned :: (Assert term, Primitive term, Witness term) => term () ()
oldfashioned = scribe ha >>> pkwCheckSigHashAll lib (privateToPublic childToKey) undefined

spendUsingSignatureUpdate :: (Assert term, Primitive term, Witness term) => term (Bit, ()) ()
spendUsingSignatureUpdate = assertl (drop (oldfashioned :: _)) (commitmentRoot @(Bit, ()) $ drop unit)

spendUsingSignature :: (Assert term, Primitive term, Witness term) => term (Bit, ()) ()
spendUsingSignature = cond (oldfashioned :: _) unit

deriving instance (Eq (Kleisli Identity (Bit, ()) ()))
deriving instance (Eq (Kleisli Identity () ()))

instance Eq (() -> Identity ()) where
    a == b = True

instance Eq ((Bit, ()) -> Identity ()) where
    a == b = True

instance MonadFail Identity where
    fail = error

instance MonadReader PrimEnv Identity where
    ask = Identity $ error "asked for primenv"
    local f = id

main :: IO ()
main = do
  print $ commitmentRoot oldfashioned
  print $ (==) @(Kleisli Identity () ()) oldfashioned oldfashioned
  print $ (==) @(Kleisli Identity (Bit, ()) ()) spendUsingSignatureUpdate spendUsingSignature
  let refprog  = spendUsingSignature    :: CommitmentRoot (Bit, ()) ()
  let prog  = spendUsingSignatureUpdate :: CommitmentRoot (Bit, ()) ()
  print prog
  print refprog
