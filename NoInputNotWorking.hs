{-# LANGUAGE StandaloneDeriving, OverloadedStrings, NamedFieldPuns #-}
module Main where

import Debug.Trace (trace)
import Prelude hiding (drop, replicate, concat, length, zipWith, fail, take, not)
import Data.Maybe (fromJust)
import Data.Either (fromLeft, fromRight, isLeft, isRight)
import Data.ByteString (replicate, concat, ByteString)
import Data.ByteString.Lazy (fromStrict, toStrict)
import Data.ByteString.Short (fromShort)
import qualified Data.ByteString.Lazy (ByteString)
import Simplicity.LibSecp256k1.Schnorr (XOnlyPubKey(..), Sig(Sig))
import Crypto.Secp256k1 (SecKey, secKey)
import Control.Arrow (runKleisli, Kleisli(Kleisli))
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad (join)
import Control.Monad.Except (runExceptT, ExceptT)
import qualified GHC.Word (Word32)
import GHC.Arr (array, (!), elems)
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
deriving instance Eq Sig

commRootToBS :: Hash256 -> Data.ByteString.Lazy.ByteString
commRootToBS = fromStrict . fromShort . hash256

mysigtxout n = TxOutput {txoValue=3000, txoScript=commRootToBS $ commitmentRoot (spendUsingSignature (toInteger n + 0) sl)}
    where
        sl = sigLock undefined

scriptToWord256 :: Script -> Word256
scriptToWord256 x = (fromRight (error $ "couldn't decode: " ++ show x)) . decode . toStrict $ x

txOutputToOutpoint :: TxOutput -> Outpoint
txOutputToOutpoint TxOutput {txoValue, txoScript} = Outpoint {opHash=numAsHash (scriptToWord256 txoScript), opIndex=(100 :: GHC.Word.Word32)}

genPrimEnv :: Lock -> Lock -> PrimEnv
genPrimEnv lockTime inLockTime =
    fromJust $ primEnv
        SigTx { sigTxVersion = 2, sigTxIn = sigtxin, sigTxOut = sigtxout, sigTxLock = lockTime}
        1 -- currentIndex
        (numAsHash 4) -- scriptCMR
    where
        sigtxout = array (1,1) [(1,TxOutput {txoValue=3000, txoScript=commRootToBS $ commitmentRoot (spendUsingSignature (toInteger lockTime + 1) $ sigLock undefined)})]
        sigtxin = array
            (0,1) -- start bound, end bound, inclusive
            -- [(index, value)]
            [(0,SigTxInput {sigTxiPreviousOutpoint=Outpoint {opHash=numAsHash 0, opIndex=(100 :: GHC.Word.Word32)}, sigTxiValue=1, sigTxiSequence=32189})
            ,(1,SigTxInput {sigTxiPreviousOutpoint=txOutputToOutpoint $ mysigtxout inLockTime, sigTxiValue=1, sigTxiSequence=12908})]

--lockTimeAtLeast :: Integer -> Kleisli MyMonad () Bit
lockTimeAtLeast n = scribe (toWord32 (n - 1)) &&& primitive LockTime >>> subtractor word32 >>> oh -- oh grabs underflow bit

--spendUsingSignature :: Sig -> Kleisli MyMonad () ()
spendUsingSignature n sig =
  let
    --seqMatch = primitive CurrentSequence &&& scribe seqToMatch >>> eq
    lockTimeMatch = lockTimeAtLeast n
  in
    --do env <- MonadReader.ask
    --assert seqMatch &&&
    assert lockTimeMatch &&& checkSig pubB sig >>> oh

otherSig = mkSig private $ replicate 32 32

fetchSigHash :: ReaderT PrimEnv Maybe (Either e Hash)
fetchSigHash = runExceptT $ runKleisli (sigHashNoInput lib) ()


sigLock :: PrimEnv -> Sig
sigLock primEnv = mkSig private (simpleHashToByteString $ ha)
  where
    eitherHa :: Either e Hash
    eitherHa = fromJust $ runReaderT fetchSigHash primEnv
    ha :: Hash
    ha = fromRight (error "couldn't calculate sighash") eitherHa

type MinSpendBlockHeight = Integer

type UTXOs = Map Outpoint (TxOutput, MinSpendBlockHeight)

spendUTXOWith :: UTXOs -> PrimEnv -> (MinSpendBlockHeight -> PrimEnv -> (CommitmentRoot () (), Kleisli (ExceptT String (ReaderT PrimEnv (Either String))) () ())) -> MinSpendBlockHeight -> [Either UTXOs String]
spendUTXOWith utxos primenv getProgs spendingHeight =
  let
    (prog, prog2) = getProgs spendingHeight primenv
    --prog = spendUsingSignature sig
    reader :: ReaderT PrimEnv (Either String) (Either String ())
    reader = runExceptT $ runKleisli prog2 ()
    scriptExecutionResult :: Either String ()
    scriptExecutionResult = join $ runReaderT reader primenv
    spendingScript :: Script
    spendingScript = commRootToBS $ commitmentRoot prog--(spendUsingSignature sig)
    lock :: Lock
    lock = sigTxLock . envTx $ primenv
  in
    do
        prevout <- elems $ sigTxIn . envTx $ primenv
        thisout <- elems $ sigTxOut . envTx $ primenv
        return $ spendUTXO utxos thisout (sigTxiPreviousOutpoint prevout) spendingScript scriptExecutionResult spendingHeight (toInteger (trace (show lock) lock))

spendUTXO :: UTXOs -> TxOutput -> Outpoint -> Script -> Either String () -> MinSpendBlockHeight -> MinSpendBlockHeight -> Either UTXOs String
spendUTXO utxos thisout prevout spendingScript scriptExecutionResult spendingBlockHeight newSpendingHeight =
  let
    newOutpoint :: Outpoint
    newOutpoint = txOutputToOutpoint thisout
    newUtxos = insert newOutpoint (thisout, newSpendingHeight) (delete prevout utxos)
  in
    case utxos !? prevout of
    Nothing -> Right "no such prevout"
    Just (TxOutput {txoScript}, minSpendBlockHeight) ->
        --if spendingScript == txoScript then
        if minSpendBlockHeight <= spendingBlockHeight then
            case scriptExecutionResult of
            Right _ -> Left newUtxos
            Left err -> Right err
        else
            Right $ "spending block height not sufficient"
            --Right $ "didn't spend right program"


spendSig n primenv = ((spendUsingSignature n $ sigLock undefined),
                      (spendUsingSignature n $ sigLock primenv))
spendOther n primenv = (spendUsingSignature 0 otherSig, spendUsingSignature 0 otherSig)

initUtxos :: UTXOs
initUtxos = fromList [(outpoint, (mysigtxout 3, 3))]
            where
              outpoint = txOutputToOutpoint $ mysigtxout 3

spent :: UTXOs
spent = fromLeft (error "expected left") $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 4 3) spendSig 4

main :: IO ()
main = do
  print spent
  defaultMain (testGroup "unit tests"
      [ testCase "cannot spend with 3"                            $ assertBool "should be right" $ isRight $ sequenceA $ spendUTXOWith spent (genPrimEnv 3 5) spendSig 3
      , testCase "can    spend with 4"                            $ assertBool "should be left"  $ isLeft $ sequenceA $ spendUTXOWith spent (genPrimEnv 4 5) spendSig 4
      , testCase "can    spend with 5"                            $ assertBool "should be left"  $ isLeft  $ sequenceA $ spendUTXOWith spent (genPrimEnv 5 5) spendSig 5
      , testCase "can    spend with 6"                            $ assertBool "should be left"  $ isLeft  $ sequenceA $ spendUTXOWith spent (genPrimEnv 6 5) spendSig 6
      , testCase "can    spend with 7"                            $ assertBool "should be left"  $ isLeft  $ sequenceA $ spendUTXOWith spent (genPrimEnv 7 5) spendSig 7
      , testCase "cannot spend with 7 and wrong minimum locktime" $ assertBool "should be right" $ isRight $ sequenceA $ spendUTXOWith spent (genPrimEnv 7 6) spendSig 7
      , testCase "cannot spend initial with 2"                    $ assertBool "should be right" $ isRight $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 2 3) spendSig 2
      , testCase "cannot spend initial with 2/5"                  $ assertBool "should be right" $ isRight $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 2 3) spendSig 5
      , testCase "can    spend initial with 3"                    $ assertBool "should be left"  $ isLeft  $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 3 3) spendSig 3
      , testCase "can    spend initial with 4"                    $ assertBool "should be left"  $ isLeft  $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 4 3) spendSig 4
      , testCase "invalid sig fails"                              $ assertBool "should be right" $ isRight $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 4 3) spendOther 4
      , testCase "cannot spend initial with 4 and wrong locktime" $ assertBool "should be right" $ isRight $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 4 4) spendSig 4
      , testCase "can    spend initial with 5"                    $ assertBool "should be left"  $ isLeft  $ sequenceA $ spendUTXOWith initUtxos (genPrimEnv 5 3) spendSig 5
      ])
