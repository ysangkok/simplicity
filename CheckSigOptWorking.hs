{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts, TypeApplications #-}

module Main where

import Prelude hiding (drop, replicate, concat, length, zipWith)
import Data.Bits (bit, (.|.))
import Data.ByteString (replicate, concat, ByteString, length, pack, zipWith, unpack)
import Data.Either (fromRight)
--import Data.Functor.Identity (Identity(Identity))
import Data.Maybe (fromJust)
import Data.Serialize (encode, decode)

import Debug.Trace

import Control.Arrow (Kleisli(Kleisli), runKleisli, (<<<), (>>>), (&&&))
import Control.Monad (unless)
import qualified Control.Monad.Fail as Fail
import Control.Monad.Reader (MonadReader(ask,local),asks,ReaderT,runReaderT)
import GHC.Arr (array)
import GHC.Word (Word64, Word8, Word32)

import Crypto.Secp256k1 (signMsgSchnorr, msg, secKey, exportSchnorrSig, derivePubKey, SecKey, xOnlyPubKeyFromPubKey, exportXOnlyPubKey, importXOnlyPubKey, importSchnorrSig, verifyMsgSchnorr)

import Lens.Family2 (review)

import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive (PrimEnv, primEnv, Prim(Version), primSem)
import Simplicity.Bitcoin.Programs.CheckSigHashAll (pkwCheckSigHashAll, Hash, lib, sigHashAll)
import Simplicity.Bitcoin.Term (Primitive, primitive, drop, assertl, assertr, unit, witness, Simplicity)
import Simplicity.Digest (hash0, be256)
import Simplicity.Ty.Bit (Bit, toBit)
import Simplicity.Ty.Word (Vector16, toWord1, word1, Word1, fromWord256, Word256)
import Simplicity.Programs.Word (adder)
import Simplicity.LibSecp256k1.Schnorr (Sig(..), XOnlyPubKey(..))
import Simplicity.MerkleRoot (commitmentRoot)

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

privateToPublic :: SecKey -> XOnlyPubKey
privateToPublic = fromRight (error "could not decode pubkey") . decode . exportXOnlyPubKey . (flip xOnlyPubKeyFromPubKey 1) . derivePubKey

private :: SecKey
private = fromJust $ secKey $ concat [replicate 31 0, "\x01"]

pubB ::XOnlyPubKey
pubB = privateToPublic private

mkSig :: ByteString -> Sig
mkSig sigHash = if length sigHash /= 32 then error ("not 32: " ++ (show sigHash)) else fromRight (error "could not decode schnorr sig") (decode $ exportSchnorrSig (signMsgSchnorr private (fromJust $ msg $ sigHash)))

fun :: (Int, Word8) -> Word64 -> Word64
fun (idx, thisBit) acc = acc .|. (case thisBit of
  1 -> bit (fromIntegral idx)
  0 -> 0
  _ -> error "byte not 0 or 1")

simpleHashToByteString :: Hash -> ByteString
simpleHashToByteString ((v4,v3),(v2,v1)) = concat [encode $ foldr fun 0 (zip [0..63] (reverse $ unpack $ encode v4)),
                                                   encode $ foldr fun 0 (zip [0..63] (reverse $ unpack $ encode v3)),
                                                   encode $ foldr fun 0 (zip [0..63] (reverse $ unpack $ encode v2)),
                                                   encode $ foldr fun 0 (zip [0..63] (reverse $ unpack $ encode v1))]

{-# NOINLINE checkSig #-}
checkSig pubK sig = pkwCheckSigHashAll lib pubK sig <<< sigHashAll lib

validateSigOrFail :: XOnlyPubKey -> Sig -> Kleisli MyMonad () ()
validateSigOrFail pub sig = Kleisli $ \unit -> do
  hsh <- runKleisli (sigHashAll lib) ()
  let b32pub = encode pub
  let b64sig = encode sig
  let b32msg = simpleHashToByteString hsh
  unless (length b32pub == 32) (fail "bad pub length")
  unless (length b64sig == 64) (fail "bad sig length")
  unless (length b32msg == 32) (fail "bad msg length")
  let Just nativePub = importXOnlyPubKey b32pub
  let Just nativeSig = importSchnorrSig b64sig
  let Just nativeMsg = msg b32msg
  unless (verifyMsgSchnorr nativePub nativeSig nativeMsg) (fail "sig did not verify")
  return ()

{-# RULES
"checkSigGone" forall pub sig. checkSig pub sig = validateSigOrFail pub sig
  #-}

minicalc :: MyMonad ()
minicalc = do
  env <- ask :: MyMonad PrimEnv
  ha <- runKleisli (sigHashAll lib) ()
  let sig = mkSig $ simpleHashToByteString ha
  unit <- runKleisli (checkSig pubB sig) ()
  pure ()

main :: IO ()
main = do
  output <- (runReaderT $ runMyMonad $ minicalc) primenv
  print output
  pure ()
