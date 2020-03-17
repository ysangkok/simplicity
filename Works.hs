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
import Control.Monad ((<=<))
import qualified Control.Monad.Fail as Fail
import Control.Monad.Reader (MonadReader(ask,local),asks,ReaderT,runReaderT)
import GHC.Arr (array)
import GHC.Word (Word64, Word8, Word32)

import Crypto.Secp256k1 (signMsgSchnorr, msg, secKey, exportSchnorrSig, derivePubKey, SecKey, xOnlyPubKeyFromPubKey, exportXOnlyPubKey)

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

privateToPublic = fromRight (error "could not decode pubkey") . decode . exportXOnlyPubKey . (flip xOnlyPubKeyFromPubKey 1) . derivePubKey

private :: SecKey
private = fromJust $ secKey $ concat [replicate 31 0, "\x01"]

--sigA = Sig (read "0") (read "1")
--sigB = Sig (read "1") (read "0")
--pubA = XOnlyPubKey (read "1")

pubB ::XOnlyPubKey
pubB = privateToPublic private
--oneOf2 = (witness (toBit False) &&& unit >>> assertl (drop (pkwCheckSigHashAll lib pubB sigB)) (commitmentRoot @((), ()) (drop (pkwCheckSigHashAll lib pubA sigA))) )

--calc1 = primitive Version

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
--simpleHashToByteString :: Hash -> ByteString
--simpleHashToByteString = encode . (review be256) . fromWord256


minicalc :: MyMonad (Word1, ((Vector16 Bit, Vector16 Bit), ()))
minicalc = do
  env <- ask :: MyMonad PrimEnv
  let l = lib
  ha <- runKleisli (sigHashAll l) ()
  let sig = mkSig $ simpleHashToByteString ha
  let checkSig = pkwCheckSigHashAll l pubB (trace ("sig: " ++ (show $ encode sig)) sig) :: Kleisli MyMonad Hash ()
  (runKleisli $ beginMyProgram <<< ((primitive Version) &&& (checkSig <<< sigHashAll l) )) ()

--primcalc :: PrimEnv -> IO (Vector16 Bit, Vector16 Bit)
primcalc = runReaderT $ runMyMonad $ minicalc

main :: IO ()
main = do
  output <- primcalc primenv
  print output
  --print (fromJust $ primSem Version () primenv)
  pure ()

beginMyProgram = Kleisli $ \x -> do
    env <- ask :: MyMonad PrimEnv
    let y = adder word1
    pure (trace (show (y (toWord1 0, toWord1 1))) (toWord1 1, x))
