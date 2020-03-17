{-# LANGUAGE StandaloneDeriving, OverloadedStrings, NamedFieldPuns, TypeApplications, PartialTypeSignatures #-}
module Main where

import Debug.Trace (trace)
import Prelude hiding (drop, replicate, concat, length, zipWith, fail, take, not, or)
import Data.List (intercalate, length)
import Data.Maybe (fromJust)
import Data.Either (fromRight)
import Data.ByteString (replicate, concat, ByteString)
import Data.ByteString.Lazy (fromStrict, toStrict)
import Data.ByteString.Short (fromShort)
import qualified Data.ByteString.Lazy (ByteString)
import Simplicity.LibSecp256k1.Schnorr (XOnlyPubKey(..), Sig(Sig))
import Control.Arrow (runKleisli) --, Kleisli(Kleisli))
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad (join, unless)
import Control.Monad.Except (runExceptT)
import qualified GHC.Word (Word32, Word64)
import GHC.Arr (array, elems)
--import Data.Map.Strict (fromList, (!?), Map, insert, delete)

import Lens.Family2 (review, over)

import Simplicity.MerkleRoot (commitmentRoot, CommitmentRoot)
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive (Prim(..), PrimEnv, primEnv, envTx)
import Simplicity.Bitcoin.Term (primitive, Primitive)
import Simplicity.Digest (be256, hash256, Hash256)
import Simplicity.Programs.Bit (assert, cond, toBit, Bit)
import Simplicity.Programs.Generic (scribe) -- eq
import Simplicity.Programs.Word (subtractor)
import Simplicity.Term.Core ((>>>), (&&&), oh, iden, assertr, drop, witness, unit, assertl, Witness, Assert, TyC)
import Simplicity.Ty.Word (Word32, toWord32, word32)
import qualified Simplicity.Ty
import Simplicity.Word (Word256)

import Data.Serialize (decode)

import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

import CheckSigNoInput (lib, mkSig, checkSig, simpleHashToByteString, privateToPublic, sigHashNoInput, Hash)

import Crypto.Secp256k1 (SecKey, secKey)
import Crypto.Secp256k1 (schnorrTweakAddPubKey, createXOnlyPubKey, exportXOnlyPubKey, tweak, schnorrTweakAddSecKey, testTweakXOnlyPubKey, signMsgSchnorr, verifyMsgSchnorr, msg)

import Network.Haskoin.Keys (makeXPrvKey, hardSubKey, xPrvKey, getSecKey, XPrvKey, KeyIndex)

import Data.ByteString.Base16 (encode)

root :: XPrvKey
root = makeXPrvKey $ concat [replicate 32 1]

childToKey :: XPrvKey -> SecKey
childToKey = fromJust . secKey . getSecKey . xPrvKey

numAsHash :: Word256 -> Hash256
numAsHash = review (over be256)

deriving instance Eq Outpoint
deriving instance Ord Outpoint

deriving instance Eq TxOutput
deriving instance Eq Sig

deriving instance Show Sig

commRootToBS :: Hash256 -> Data.ByteString.Lazy.ByteString
commRootToBS = fromStrict . fromShort . hash256

--scriptToWord256 :: Script -> Word256
--scriptToWord256 x = (fromRight (error $ "couldn't decode: " ++ show x)) . decode . toStrict $ x

--txOutputToOutpoint :: TxOutput -> Outpoint
--txOutputToOutpoint TxOutput {txoScript} = Outpoint {opHash=numAsHash (scriptToWord256 txoScript), opIndex=(100 :: GHC.Word.Word32)}

--lockTimeLarger :: Integer -> Kleisli MyMonad () Bit
lockTimeLarger n = scribe (toWord32 (toInteger n)) &&& primitive LockTime >>> subtractor word32 >>> oh -- oh grabs underflow bit

no_locktime_and_update :: Bit
no_locktime_and_update = toBit True

use_locktime_and_settle :: Bit
use_locktime_and_settle = toBit False

spendUsingSignatureUpdate :: (TyC a, TyC b, Assert term, Primitive term, Witness term) =>
                                   p1 -> PubSigDouble -> p2 -> p3 -> term (Either a b, ()) ()
spendUsingSignatureUpdate
    n
    (PubSigDouble{pubA=updatePubA, pubB=updatePubB, sig=updateSig, sig2=updateSig2})
    settlePubA settlePubB
    =
        let
          --seqMatch = primitive CurrentSequence &&& scribe seqToMatch >>> eq
          checkUpdateSigs = checkSig updatePubA updateSig &&& checkSig updatePubB updateSig2 >>> oh
        in
          --do env <- MonadReader.ask
          --assert seqMatch &&&
          assertl (drop checkUpdateSigs) (commitmentRoot @(Bit, ()) @() $ drop unit)

--spendUsingSignature :: Integer -> Sig -> Kleisli MyMonad () ()
spendUsingSignature
    n
    (PubSigDouble{pubA=updatePubA, pubB=updatePubB, sig=updateSig, sig2=updateSig2})
    (PubSigDouble{pubA=settlePubA, pubB=settlePubB, sig=settleSig, sig2=settleSig2})
    =
        let
          --seqMatch = primitive CurrentSequence &&& scribe seqToMatch >>> eq
          checkUpdateSigs = checkSig updatePubA updateSig &&& checkSig updatePubB updateSig2 >>> oh
        in
          --do env <- MonadReader.ask
          --assert seqMatch &&&
          cond checkUpdateSigs unit

otherSig = mkSig (fromJust $ secKey (replicate 32 32)) $ replicate 32 32

fetchSigHash :: ReaderT PrimEnv Maybe (Either e Hash)
fetchSigHash = runExceptT $ runKleisli (sigHashNoInput lib) ()

sigLock :: PrimEnv -> SecKey -> Sig
sigLock primenv privateKey = mkSig privateKey (simpleHashToByteString $ ha)
  where
    eitherHa :: Either e Hash
    eitherHa = fromJust $ runReaderT fetchSigHash primenv
    ha :: Hash
    ha = fromRight (error "couldn't calculate sighash") eitherHa

data Balances = Balances {
    balA :: GHC.Word.Word64
  , balB :: GHC.Word.Word64
}

genPrimEnv :: Lock -> Data.ByteString.Lazy.ByteString -> PrimEnv
genPrimEnv lockTime outputScript =
    fromJust $ primEnv
        SigTx { sigTxVersion = 2, sigTxIn = sigtxin, sigTxOut = sigtxout, sigTxLock = lockTime}
        1 -- currentIndex
        (numAsHash 4) -- scriptCMR
    where
        sigtxout = array (1,1) [(1,TxOutput {txoValue=1, txoScript=outputScript})]
        sigtxin = array
            (0,1) -- start bound, end bound, inclusive
            -- [(index, value)]
            [(0,SigTxInput {sigTxiPreviousOutpoint=Outpoint {opHash=numAsHash 0, opIndex=(100 :: GHC.Word.Word32)}, sigTxiValue=1, sigTxiSequence=32189})
            ,(1,SigTxInput {sigTxiPreviousOutpoint=undefined, sigTxiValue=1, sigTxiSequence=12908})] -- undefined works only because of NoInput

scriptExecutionResult chosen_branch prog2 primenv =
    let
        reader :: ReaderT PrimEnv (Either String) (Either String ())
        reader = runExceptT $ runKleisli prog2 (chosen_branch, ())
    in
        join $ runReaderT reader primenv

data PubSigDouble = PubSigDouble {
    sig :: Sig
  , sig2 :: Sig
  , pubA :: XOnlyPubKey
  , pubB :: XOnlyPubKey
}

pubsAndSigs :: PrimEnv -> XPrvKey -> PubSigDouble
pubsAndSigs primenv node =
    let
        priA = childToKey $ hardSubKey node 0
        priB = childToKey $ hardSubKey node 1
    in
        PubSigDouble {
            sig =  sigLock primenv priA
          , sig2 = sigLock primenv priB
          , pubA = privateToPublic priA
          , pubB = privateToPublic priB
        }

checkPrevout prog utxoSet =
    if
        elem (commRootToBS $ commitmentRoot prog) utxoSet
    then
        Right ()
    else
        Left "program getting spent not in utxo set"

checkPrevoutAndScriptExec script_input prog2 primenv utxoSet prog = do
    -- this is the Either monad, so will short-circuit on first Left
    checkPrevout prog utxoSet
    scriptExecutionResult script_input prog2 primenv
    return $ map txoScript (elems $ sigTxOut $ envTx $ primenv)

genKey :: [KeyIndex] -> XOnlyPubKey
genKey x = privateToPublic $ childToKey $ foldl hardSubKey root x

settlingTriedUtxoSet :: Either String [Script]
settlingTriedUtxoSet =
  let
    inputBlockHeight = 20
    spendingBlockHeight = inputBlockHeight + 1
    outputScript :: CommitmentRoot (Bit, ()) ()
    outputScript = spendUsingSignature spendingBlockHeight (PubSigDouble {sig=undefined, sig2=undefined, pubA=genKey [100,0], pubB=genKey [100,1]})
                                                           (PubSigDouble {sig=undefined, sig2=undefined, pubA=genKey [200,0], pubB=genKey [200,1]})
    primenv = genPrimEnv spendingBlockHeight (commRootToBS $ commitmentRoot $ outputScript)
    updateSigs = pubsAndSigs primenv (hardSubKey root 0) -- update is used with locktime
    settleSigs = pubsAndSigs primenv (hardSubKey root 1) -- settle is used w/o  locktime
    prog :: CommitmentRoot (Bit, ()) ()
    prog  = spendUsingSignature inputBlockHeight updateSigs settleSigs :: _--otherSig
    prog2 = spendUsingSignature inputBlockHeight updateSigs settleSigs :: _--otherSig
    --(chosen_branch, str) <- [(use_locktime_and_settle, "using locktime"), (no_locktime_and_update, "just multisig")]

    -- we pretend the channel parties have already opened the channel and committed to prog
    utxoSet = [commRootToBS $ commitmentRoot prog]

    newUtxoSet = checkPrevoutAndScriptExec use_locktime_and_settle prog2 primenv utxoSet prog
    -- newUtxoSet contains outputScript
  in
    newUtxoSet

updateChannel :: [Script] -> Either String ()
updateChannel utxos = do
    -- locktime doesn't matter since we are updating, not settling
    let primenv = genPrimEnv (-1) ("bogus output script")
    let updateSigs = pubsAndSigs primenv (hardSubKey root 100)

    -- TODO remove these two
    let settleSigs = let
                         priA = childToKey $ hardSubKey (hardSubKey root 200) 0
                         priB = childToKey $ hardSubKey (hardSubKey root 200) 1
                     in
                         PubSigDouble {
                             sig =  sigLock primenv priA -- TODO why can't this be otherSig. we are not settling, shouldn't need sigs for it
                           , sig2 = sigLock primenv priB -- TODO ditto
                           , pubA = privateToPublic priA
                           , pubB = privateToPublic priB
                         }
    let refprog  = spendUsingSignature    21 updateSigs settleSigs :: CommitmentRoot (Bit, ()) ()
    let prog  = spendUsingSignatureUpdate 21 updateSigs (genKey [200,0]) (genKey [200,1]) :: CommitmentRoot (Bit, ()) ()
    let prog2 = spendUsingSignatureUpdate 21 updateSigs (genKey [200,0]) (genKey [200,1])
    newUtxoSet <- checkPrevoutAndScriptExec no_locktime_and_update prog2 primenv utxos (trace (intercalate "\n" $ map show [("pruned", prog), ("ref", refprog)]) prog)
    return ()

main :: IO ()
main = do
  ------A SCHNORR TEST---------------------------------
  let Just pri = secKey $ replicate 32 32
  let internal_pk = createXOnlyPubKey pri
  let Just twea = tweak $ exportXOnlyPubKey internal_pk -- serialize
  let Just (output_pk, is_negated) = schnorrTweakAddPubKey internal_pk twea

  -- key spend
  let Just tweak_sec = schnorrTweakAddSecKey pri twea
  let Just msgToSign = msg $ replicate 32 80
  let sig = signMsgSchnorr tweak_sec msgToSign
  unless (verifyMsgSchnorr output_pk sig msgToSign) $ error "couldn't validate signature during key spend"

  -- script spend
  unless (testTweakXOnlyPubKey output_pk is_negated internal_pk twea) $ error "couldn't validate tweak during script spend"

  ------OVERRIDING ELTOO SETTLE WITH UPDATE------------
  let Right utxoSet = settlingTriedUtxoSet
  unless (length utxoSet == 1) $ error "unexpected length of utxoset"
  putStrLn $ intercalate "\n" ([show $ updateChannel utxoSet])

  --defaultMain (testGroup "unit tests"
  --    [ testCase "cannot spend with 3" $ sigLock primenv @?= Sig 60513706556935611167105236925971329838165992291171675165890898807847733630681 7602309685439530741286300402710243286713414215401783614188167693970881110854
  --    ])
