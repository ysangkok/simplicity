{-# LANGUAGE StandaloneDeriving, OverloadedStrings, NamedFieldPuns #-}
module Main where

import Prelude hiding (drop, replicate, concat, length, zipWith, toInteger, fail, take, not)
import Data.Maybe (fromJust)
import Data.Either (fromRight, isRight)
import Data.ByteString (replicate, concat, ByteString)
import Data.ByteString.Lazy (fromStrict, toStrict)
import Data.ByteString.Short (fromShort)
import qualified Data.ByteString.Lazy (ByteString)
import Simplicity.LibSecp256k1.Schnorr (XOnlyPubKey(..), Sig)
import Crypto.Secp256k1 (SecKey, secKey)
import Control.Arrow (runKleisli, Kleisli(Kleisli))
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad (join)
import Control.Monad.Except (runExceptT, ExceptT)
import qualified GHC.Word (Word32)
import GHC.Arr (array, (!))
import Data.Map.Strict (fromList, (!?), Map, insert, delete)

import Lens.Family2 (review, over)

import Simplicity.MerkleRoot (commitmentRoot, CommitmentRoot)
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive (Prim(..), PrimEnv, primEnv, envTx)
import Simplicity.Bitcoin.Term (primitive)
import Simplicity.Digest (be256, hash256, Hash256)
import Simplicity.Programs.Bit (assert)
import Simplicity.Programs.Generic (scribe, eq)
import Simplicity.Programs.Word (subtractor, adder)
import Simplicity.Term.Core ((>>>), (&&&), oh)
import Simplicity.Ty.Word (Word32, fromWord32, toWord32, fromWord256, word32)
import Simplicity.Ty.Bit (Bit)
import Simplicity.Word (Word256)

import Data.Serialize (decode)

import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

import CheckSigNoInput (MyMonad, lib, mkSig, checkSig, simpleHashToByteString, privateToPublic, sigHashNoInput, Hash)

private :: SecKey
private = fromJust $ secKey $ concat [replicate 31 0, "\x01"]

pubB :: XOnlyPubKey
pubB = privateToPublic private

pubA :: XOnlyPubKey
pubA = privateToPublic $ fromJust $ secKey $ concat [replicate 31 0, "\x02"]

numAsHash :: Word256 -> Hash256
numAsHash = review (over be256)

deriving instance Eq Outpoint
deriving instance Ord Outpoint

deriving instance Eq TxOutput

commRootToBS :: Hash256 -> Data.ByteString.Lazy.ByteString
commRootToBS = fromStrict . fromShort . hash256

outpoint = Outpoint {opHash=numAsHash $ scriptToWord256 $ commRootToBS $ commitmentRoot $ spendUsingSignature sig, opIndex=(110 :: GHC.Word.Word32)}

scriptToWord256 :: Script -> Word256
scriptToWord256 x = (fromRight (error $ "couldn't decode: " ++ show x)) . decode . toStrict $ x

txOutputToOutpoint :: TxOutput -> Outpoint
txOutputToOutpoint TxOutput {txoValue, txoScript} = Outpoint {opHash=numAsHash (scriptToWord256 txoScript), opIndex=(100 :: GHC.Word.Word32)}

genPrimEnv :: Lock -> PrimEnv
genPrimEnv lockTime =
    fromJust $ primEnv
        SigTx { sigTxVersion = 2, sigTxIn = sigtxin, sigTxOut = sigtxout, sigTxLock = lockTime}
        1 -- currentIndex
        (numAsHash 4) -- scriptCMR
    where
        sigtxout = array (1,1) [(1,TxOutput {txoValue=3000, txoScript=commRootToBS $ commitmentRoot (spendUsingSignature sig)})]
        sigtxin = array
            (0,1) -- start bound, end bound, inclusive
            -- [(index, value)]
            [(0,SigTxInput {sigTxiPreviousOutpoint=Outpoint {opHash=numAsHash 0, opIndex=(100 :: GHC.Word.Word32)}, sigTxiValue=1, sigTxiSequence=32189})
            ,(1,SigTxInput {sigTxiPreviousOutpoint=outpoint, sigTxiValue=1, sigTxiSequence=12908})]

--lockTimeAtLeast :: Integer -> Kleisli MyMonad () Bit
lockTimeAtLeast n = scribe (toWord32 (n - 1)) &&& primitive LockTime >>> subtractor word32 >>> oh -- oh grabs underflow bit

--spendUsingSignature :: Sig -> Kleisli MyMonad () ()
spendUsingSignature sig =
  let
    --seqMatch = primitive CurrentSequence &&& scribe seqToMatch >>> eq
    lockTimeMatch = lockTimeAtLeast 4
  in
    --do env <- MonadReader.ask
    --assert seqMatch &&&
    assert lockTimeMatch &&& checkSig pubB sig >>> oh

otherSig = mkSig private $ replicate 32 32

fetchSigHash :: ReaderT PrimEnv Maybe (Either e Hash)
fetchSigHash = runExceptT $ runKleisli (sigHashNoInput lib) ()

eitherHa :: Either e Hash
eitherHa = fromJust $ runReaderT fetchSigHash (genPrimEnv 4)

ha :: Hash
ha = fromRight (error "couldn't calculate sighash") eitherHa

sig :: Sig
sig = mkSig private (simpleHashToByteString $ ha)

type UTXOs = Map Outpoint TxOutput

--initBlockchain :: [(PrimEnv, UTXOs)]
--initBlockchain = []

initUtxos :: UTXOs
initUtxos = fromList [(outpoint, sigtxout)]
            where
              sigtxout = TxOutput {txoValue=3000, txoScript=commRootToBS $ commitmentRoot (spendUsingSignature sig)}

--spend :: UTXOs -> PrimEnv -> Sig -> Either String UTXOs
spendUTXOWith :: _
spendUTXOWith utxos primenv prog prog2 =
  let
    --prog = spendUsingSignature sig
    reader :: ReaderT PrimEnv (Either String) (Either String ())
    reader = runExceptT $ runKleisli prog2 ()
    prevout :: Outpoint
    prevout = sigTxiPreviousOutpoint $ (sigTxIn . envTx $ primenv) ! 1 -- index starts at 0
    thisout :: TxOutput
    thisout = (sigTxOut . envTx $ primenv) ! 1 -- index starts at 1
    Just prevtxo = utxos !? prevout
    spendingScript :: Script
    spendingScript = commRootToBS $ commitmentRoot prog--(spendUsingSignature sig)
    prevScript :: Script
    prevScript = txoScript prevtxo
    scriptExecutionResult :: Either String ()
    scriptExecutionResult = join $ runReaderT reader primenv
    newOutpoint :: Outpoint
    newOutpoint = txOutputToOutpoint thisout
    newUtxos = insert newOutpoint thisout (delete prevout utxos)
  in
    if spendingScript == prevScript then
        case scriptExecutionResult of
        Right _ -> Right newUtxos
        Left spendingScript -> Left spendingScript
    else
        Left $ "didn't spend right program"


spendSig = spendUsingSignature sig
spendOther = spendUsingSignature otherSig

main :: IO ()
main = do
  -- print $ commitmentRoot $ spendUsingSignature sig
  print $ spendUTXOWith initUtxos (genPrimEnv 4) spendSig spendSig
  defaultMain (testGroup "unit tests" [ testCase "invalid sig fails"                    $ spendUTXOWith initUtxos (genPrimEnv 4) spendOther spendOther @?= Left "sig did not verify"
                                      --, testCase "mismatching sequences fails"          $ spendUTXOWith (genPrimEnv (Params 30 4)) sig      @?= Left "Simplicity.Term.Core: assertr failed"
                                      , testCase "validates with no mismatch"           $ assertBool "should be right" (isRight $ spendUTXOWith initUtxos (genPrimEnv 4) spendSig spendSig)
                                      , testCase "checkSigNoInput validates locktime"   $ spendUTXOWith initUtxos (genPrimEnv 5) spendSig spendSig @?= Left "sig did not verify"
                                      -- TODO: test lock time check
                                      ])
