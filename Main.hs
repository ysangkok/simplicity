{-# LANGUAGE TypeApplications #-}
module Main where

import Prelude hiding (drop, replicate)
import Data.Either (fromRight)
import Data.ByteString (replicate)
import Simplicity.MerkleRoot (commitmentRoot, CommitmentRoot)
import Simplicity.Bitcoin.Term (Primitive)
import Simplicity.Programs.Bit (cond, Bit)
import Simplicity.Programs.Generic (scribe)
import Simplicity.Term.Core ((>>>), drop, unit, assertl, Witness, Assert)
import Simplicity.Ty.Word (Vector64)
import Simplicity.Bitcoin.Programs.CheckSigHashAll hiding (XOnlyPubKey, Sig)
import Data.Serialize (decode)
import Simplicity.LibSecp256k1.Schnorr (XOnlyPubKey)

pub :: XOnlyPubKey
pub = fromRight (error "no go") $ decode $ replicate 32 32

v :: Vector64 Bit
v = fromRight (error "no go") $ Data.Serialize.decode $ replicate 64 64

ha :: Hash
ha = ((v, v), (v, v))

checkSig :: (Assert term, Primitive term, Witness term) => term () ()
checkSig = scribe ha >>> pkwCheckSigHashAll lib pub undefined

p1 :: (Assert term, Primitive term, Witness term) => term (Bit, ()) ()
p1 = assertl (drop checkSig) (commitmentRoot @(Bit, ()) $ drop unit)

p2 :: (Assert term, Primitive term, Witness term) => term (Bit, ()) ()
p2 = cond checkSig unit

main :: IO ()
main = do
  let c1  = p1 :: CommitmentRoot (Bit, ()) ()
  let c2  = p2 :: CommitmentRoot (Bit, ()) ()
  print c1
  print c2
