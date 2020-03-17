{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, MultiParamTypeClasses, FlexibleContexts, TypeApplications, FlexibleInstances #-}

module CheckSigNoInput (checkSig, mkSig, privateToPublic, simpleHashToByteString, lib, sigHashNoInput, MyMonad, Hash) where

import Prelude hiding (drop, replicate, concat, length, zipWith)
import Data.Bits (bit, (.|.))
import Data.ByteString (concat, ByteString, length, unpack)
import Data.Either (fromRight)
import Data.Maybe (fromJust)
import Data.Serialize (encode, decode)
import Control.Monad.Except (ExceptT)

import Control.Arrow (Kleisli(Kleisli), runKleisli)
import Control.Monad (unless)
import Control.Monad.Reader (ReaderT)
import GHC.Word (Word64, Word8)

import Crypto.Secp256k1 (signMsgSchnorr, msg, exportSchnorrSig, SecKey, createXOnlyPubKey, exportXOnlyPubKey, importXOnlyPubKey, importSchnorrSig, verifyMsgSchnorr)

import Simplicity.Bitcoin.Primitive (PrimEnv)
import Simplicity.Bitcoin.Programs.CheckSigHashAll (pkwCheckSigHashAll, Hash, lib, sigHashAll) -- actually noInput
import Simplicity.LibSecp256k1.Schnorr (Sig(..), XOnlyPubKey(..))
import Simplicity.Term.Core ((>>>))

sigHashNoInput = sigHashAll

privateToPublic :: SecKey -> XOnlyPubKey
privateToPublic = fromRight (error "could not decode pubkey") . decode . exportXOnlyPubKey . createXOnlyPubKey

type MyMonad = ExceptT String (ReaderT PrimEnv (Either String))

-- TODO orphan instance
instance MonadFail (Either String) where
    fail = Left

mkSig :: SecKey -> ByteString -> Sig
mkSig private sigHash = if length sigHash /= 32 then error ("not 32: " ++ (show sigHash)) else fromRight (error "could not decode schnorr sig") (decode $ exportSchnorrSig (signMsgSchnorr private (fromJust $ msg $ sigHash)))

setBit :: (Int, Word8) -> Word64 -> Word64
setBit (idx, thisBit) acc = acc .|. (case thisBit of
  1 -> bit (fromIntegral idx)
  0 -> 0
  _ -> error "byte not 0 or 1")

simpleHashToByteString :: Hash -> ByteString
simpleHashToByteString ((v4,v3),(v2,v1)) = concat [encode $ foldr setBit 0 (zip [0..63] (reverse $ unpack $ encode v4)),
                                                   encode $ foldr setBit 0 (zip [0..63] (reverse $ unpack $ encode v3)),
                                                   encode $ foldr setBit 0 (zip [0..63] (reverse $ unpack $ encode v2)),
                                                   encode $ foldr setBit 0 (zip [0..63] (reverse $ unpack $ encode v1))]

{-# NOINLINE checkSig #-}
checkSig pubK sig =
    sigHashNoInput lib
    >>> pkwCheckSigHashAll lib pubK sig -- actually NoInput

validateSigOrFail :: XOnlyPubKey -> Sig -> Kleisli MyMonad () ()
validateSigOrFail pub sig = Kleisli $ \_unit -> do
  hsh <- runKleisli (sigHashNoInput lib) ()
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
