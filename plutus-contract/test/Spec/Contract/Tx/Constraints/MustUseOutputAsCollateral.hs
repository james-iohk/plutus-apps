{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
module Spec.Contract.Tx.Constraints.MustUseOutputAsCollateral(tests) where

import Control.Lens (At (at), (&), (??), (^.), (^..))
import Control.Monad (void)
import Test.Tasty (TestTree, testGroup)

import Control.Lens.Combinators (non)
import Data.Map as M
import Data.Set as S (Set, elemAt, toList)
import Data.Text qualified as Text
import Ledger qualified as L
import Ledger qualified as PSU
import Ledger.Ada qualified as Ada
import Ledger.Constraints qualified as Constraints
import Ledger.Constraints.OffChain qualified as OffCon
import Ledger.Constraints.OnChain.V1 qualified as Constraints
import Ledger.Constraints.OnChain.V2 qualified as V2.Constraints
import Ledger.Generators (someTokenValue)
import Ledger.Scripts (Redeemer, ScriptError (EvaluationError))
import Ledger.Test (asDatum, asRedeemer, someValidator, someValidatorHash)
import Ledger.Tx qualified as Tx
import Ledger.Tx.Constraints qualified as Tx.Constraints
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.ChainIndex.Emulator (diskState, unCredentialMap)
import Plutus.ChainIndex.Emulator.DiskState (addressMap)
import Plutus.Contract as Con
import Plutus.Contract.Test (assertContractError, assertFailedTransaction, assertValidatedTransactionCount,
                             changeInitialWalletValue, checkPredicateOptions, defaultCheckOptions, emulatorConfig,
                             mockWalletPaymentPubKeyHash, tx, w1, (.&&.))
import Plutus.Script.Utils.V1.Generators (alwaysSucceedValidatorHash)
import Plutus.Script.Utils.V1.Scripts qualified as PSU.V1
import Plutus.Script.Utils.V2.Scripts qualified as PSU.V2
import Plutus.Script.Utils.V2.Typed.Scripts qualified as V2.Scripts
import Plutus.Trace qualified as Trace
import Plutus.V1.Ledger.Api (Address (addressCredential))
import Plutus.V1.Ledger.Value qualified as Value
import PlutusTx qualified
import PlutusTx.Prelude qualified as P
import Wallet (WalletAPIError (InsufficientFunds))
import Wallet.Emulator.Wallet as Wallet (WalletState, chainIndexEmulatorState, ownAddress, signPrivateKeys,
                                         walletToMockWallet')

tests :: TestTree
tests =
    testGroup "MustUseOutputAsCollateral"
      [ testGroup "ledger constraints" $ [v1Tests, v2Tests] ?? ledgerSubmitTx
      --, testGroup "cardano constraints" $ [v1Tests, v2Tests] ?? cardanoSubmitTx
      ]

v1Tests :: SubmitTx -> TestTree
v1Tests sub = testGroup "Plutus V1" $
   [ v1FeaturesTests
   --, v2FeaturesNotAvailableTests
   ] ?? sub ?? PSU.PlutusV1

v2Tests :: SubmitTx -> TestTree
v2Tests sub = testGroup "Plutus V2" $
  [ v1FeaturesTests
  --, v2FeaturesTests
  ] ?? sub ?? PSU.PlutusV2

v1FeaturesTests :: SubmitTx -> PSU.Language -> TestTree
v1FeaturesTests sub t = testGroup "Plutus V1 features" $
    [ singleUseOfMustUseOutputAsCollateral
    , multipleUseOfMustUseOutputAsCollateral
    , noUseOfMustUseOutputAsCollateral
    , useOfMustUseOutputAsCollateralWithoutPlutusScript
    , contractErrorWhenMustUseOutputAsCollateralExceedsMaximumCollateralInputs
    --, contractErrorWhenMustUseOutputAsCollateralProvidesOtherWalletUtxo
    --, contractErrorWhenMustUseOutputAsCollateralProvidesScriptUtxo
    --, contractErrorWhenMustUseOutputAsCollateralProvidesLessThanRequired -- or balancer adds extra?
    -- (phase2 error can never occur)
    ] ?? sub ?? t

-- v2FeaturesTests :: SubmitTx -> PSU.Language -> TestTree
-- v2FeaturesTests sub t = testGroup "Plutus V2 features" $
--     [ successfulUseOfMustUseOutputAsCollateralWithInlineDatumWithMintedTokenV2
--     ] ?? sub ?? t

-- v2FeaturesNotAvailableTests :: SubmitTx -> PSU.Language -> TestTree
-- v2FeaturesNotAvailableTests sub t = testGroup "Plutus V2 features" $
--     [ phase1FailureWhenPayToOtherScriptV1ScriptUseInlineDatum
--     ] ?? sub ?? t

someDatum :: L.Datum
someDatum = asDatum @P.BuiltinByteString "datum"

otherDatum :: L.Datum
otherDatum = asDatum @P.BuiltinByteString "other datum"

utxoValue :: Value.Value
utxoValue = Ada.lovelaceValueOf 50_000_000

adaAmount :: Integer
adaAmount = 25_000_000

tknAmount :: Integer
tknAmount = 5_000_000

adaValue :: Value.Value
adaValue = Ada.lovelaceValueOf adaAmount

tknValueOf :: Integer -> PSU.Language -> Value.Value
tknValueOf x tc = Value.singleton (mustUseOutputAsCollateralPolicyCurrencySymbol tc) "mint-me" x

tknValue :: PSU.Language -> Value.Value
tknValue = tknValueOf tknAmount

adaAndTokenValue :: PSU.Language -> Value.Value
adaAndTokenValue = (adaValue <>) . tknValue

otherTokenValue :: Value.Value
otherTokenValue = someTokenValue "someToken" 10

w1PaymentPubKeyHash :: L.PaymentPubKeyHash
w1PaymentPubKeyHash = mockWalletPaymentPubKeyHash w1

maximumCollateralInputs :: Integer
maximumCollateralInputs = 3

trace :: Contract () Empty ContractError () -> Trace.EmulatorTrace ()
trace contract = do
    void $ Trace.activateContractWallet w1 contract
    void Trace.nextSlot

-- | Contract with a single transaction using mustUseOutputAsCollateral offchain constraint and
-- mint with policy using matching onchain constraint.
mustUseOutputAsCollateralContract :: SubmitTx -> PSU.Language -> Integer ->
                                     L.PaymentPubKeyHash -> Contract () Empty ContractError ()
mustUseOutputAsCollateralContract submitTxFromConstraints lc numberOfCollateralInputs pkh = do
    pubKeyUtxos <- utxosAt $ L.pubKeyHashAddress pkh Nothing
    let collaterealUtxos = M.keys $ M.take (fromIntegral numberOfCollateralInputs) pubKeyUtxos
        lookups1 = Constraints.unspentOutputs pubKeyUtxos
                <> mintingPolicy lc (mustUseOutputAsCollateralPolicy lc)
        tx1 = mconcat (mustUseOutputsAsCollateral collaterealUtxos)
           <> Constraints.mustMintValueWithRedeemer (asRedeemer collaterealUtxos) (tknValue lc)
    ledgerTx1 <- submitTxFromConstraints lookups1 tx1
    awaitTxConfirmed $ Tx.getCardanoTxId ledgerTx1
    where
        mustUseOutputsAsCollateral utxos = Constraints.mustUseOutputAsCollateral <$> utxos

txoRefsFromWalletState :: WalletState -> Set Tx.TxOutRef
txoRefsFromWalletState w = let
  pkCred = addressCredential $ Wallet.ownAddress w
  in w ^. chainIndexEmulatorState . diskState . addressMap . unCredentialMap . at pkCred . non mempty

-- | Valid scenario using offchain and onchain constraint mustUseOutputAsCollateral to select
-- a specific utxo to use as collateral input
singleUseOfMustUseOutputAsCollateral :: SubmitTx -> PSU.Language -> TestTree
singleUseOfMustUseOutputAsCollateral submitTxFromConstraints lc =
    let contract = mustUseOutputAsCollateralContract submitTxFromConstraints lc 1 w1PaymentPubKeyHash
    in checkPredicateOptions defaultCheckOptions
      ("Successful use of offchain and onchain mustUseOutputAsCollateral for a single " ++
       "collateral input")
      (assertValidatedTransactionCount 1 .&&.
        (tx contract
        (Trace.walletInstanceTag w1)
        (\unT -> length (Tx.getCardanoTxCollateralInputs $ Tx.EmulatorTx $ unT ^. OffCon.tx) ==  1)
        "correct number of collateral inputs"))
      (void $ trace contract)

-- | Valid scenario using offchain and onchain constraint mustUseOutputAsCollateral to select
-- multiple utxos to use as collateral input
multipleUseOfMustUseOutputAsCollateral :: SubmitTx -> PSU.Language -> TestTree
multipleUseOfMustUseOutputAsCollateral submitTxFromConstraints lc =
    let contract = mustUseOutputAsCollateralContract submitTxFromConstraints
                  lc maximumCollateralInputs w1PaymentPubKeyHash
    in checkPredicateOptions defaultCheckOptions
      ("Successful use of offchain and onchain mustUseOutputAsCollateral for the maximum " ++
       "number of allowed collateral inputs")
      (assertValidatedTransactionCount 1 .&&.
        (tx contract
        (Trace.walletInstanceTag w1)
        (\unT ->
          length (Tx.getCardanoTxCollateralInputs $ Tx.EmulatorTx $ unT ^. OffCon.tx)
            ==  fromIntegral maximumCollateralInputs)
        "correct number of collateral inputs"))
      (void $ trace contract)

-- | Valid scenario where collateral input is included by default when offchain constraint
-- mustUseOutputAsCollateral is not used
noUseOfMustUseOutputAsCollateral :: SubmitTx -> PSU.Language -> TestTree
noUseOfMustUseOutputAsCollateral submitTxFromConstraints lc =
    let contract = mustUseOutputAsCollateralContract submitTxFromConstraints lc
                    0 w1PaymentPubKeyHash

    in checkPredicateOptions defaultCheckOptions
      ("No use of offchain mustUseOutputAsCollateral still includes collateral input")
      (assertValidatedTransactionCount 1 .&&.
        (tx contract
        (Trace.walletInstanceTag w1)
        (\unT -> length (Tx.getCardanoTxCollateralInputs $ Tx.EmulatorTx $ unT ^. OffCon.tx) ==  1)
        "correct number of collateral inputs"))
      (void $ trace contract)

-- | Valid scenario where offchain constraints mustUseOutputAsCollateral is used when there
-- are no plutus scripts in the tx. Collateral input is still included in tx
useOfMustUseOutputAsCollateralWithoutPlutusScript :: SubmitTx -> PSU.Language -> TestTree
useOfMustUseOutputAsCollateralWithoutPlutusScript submitTxFromConstraints _ =
    let contract = do
            ownPkh <- ownPaymentPubKeyHash
            pubKeyUtxos <- utxosAt $ L.pubKeyHashAddress ownPkh Nothing
            let utxo = head $ (M.keys $ M.take 1 pubKeyUtxos)
                lookups1 = Constraints.unspentOutputs pubKeyUtxos
                tx1 = Constraints.mustUseOutputAsCollateral utxo
                  <> Constraints.mustPayToPubKey ownPkh (Ada.adaValueOf 5)
            ledgerTx1 <- submitTxFromConstraints lookups1 tx1
            awaitTxConfirmed $ Tx.getCardanoTxId ledgerTx1

    in checkPredicateOptions defaultCheckOptions
      ("Use of offchain mustUseOutputAsCollateral when there are no plutus scripts in tx " ++
      "still includes collateral input")
      (assertValidatedTransactionCount 1 .&&.
        (tx contract
        (Trace.walletInstanceTag w1)
        (\unT -> length (Tx.getCardanoTxCollateralInputs $ Tx.EmulatorTx $ unT ^. OffCon.tx) ==  1)
        "correct number of collateral inputs"))
      (void $ trace contract)

-- | Contract error scenario when offchain constraint mustUseOutputAsCollateral is used to exceed
-- allowed maximum collatereal inputs (network protocol param)
contractErrorWhenMustUseOutputAsCollateralExceedsMaximumCollateralInputs
    :: SubmitTx
    -> PSU.Language
    -> TestTree
contractErrorWhenMustUseOutputAsCollateralExceedsMaximumCollateralInputs submitTxFromConstraints lc =
    let moreThanMaximumCollateralInputs = (succ maximumCollateralInputs)
        contract = mustUseOutputAsCollateralContract submitTxFromConstraints lc
                    moreThanMaximumCollateralInputs w1PaymentPubKeyHash
      in checkPredicateOptions defaultCheckOptions
      ("Ledger error when offchain mustUseOutputAsCollateralToSatisfyAllCollateral is used more " ++
      "than maximum number of allowed collateral inputs")
      (assertFailedTransaction
        (\_ err ->
          case err of {PSU.CardanoLedgerValidationError msg ->
              Text.isInfixOf "TooManyCollateralInputs" msg; _ -> False  })
        .&&.
        tx contract
          (Trace.walletInstanceTag w1)
          (\unT ->
            length (Tx.getCardanoTxCollateralInputs $ Tx.EmulatorTx $ unT ^. OffCon.tx)
              ==  fromIntegral moreThanMaximumCollateralInputs)
          "correct number of collateral inputs")
      (void $ trace contract)

data UnitTest
instance Scripts.ValidatorTypes UnitTest

mkMustUseOutputAsCollateralPolicy :: (Constraints.TxConstraints () () -> sc -> Bool) -> [Tx.TxOutRef] -> sc -> Bool
mkMustUseOutputAsCollateralPolicy checkScriptContext txOutRefs = checkScriptContext (P.mconcat mustUseOutputsAsCollateral)
    where
        mustUseOutputsAsCollateral = Constraints.mustUseOutputAsCollateral P.<$> txOutRefs

mustUseOutputAsCollateralPolicyV1 :: L.MintingPolicy
mustUseOutputAsCollateralPolicyV1 = L.mkMintingPolicyScript $$(PlutusTx.compile [||wrap||])
    where
        checkedMkMustUseOutputAsCollateralPolicy = mkMustUseOutputAsCollateralPolicy Constraints.checkScriptContext
        wrap = Scripts.mkUntypedMintingPolicy checkedMkMustUseOutputAsCollateralPolicy

mustUseOutputAsCollateralPolicyV2 :: L.MintingPolicy
mustUseOutputAsCollateralPolicyV2 = L.mkMintingPolicyScript $$(PlutusTx.compile [||wrap||])
    where
        checkedMkMustUseOutputAsCollateralPolicy = mkMustUseOutputAsCollateralPolicy V2.Constraints.checkScriptContext
        wrap = V2.Scripts.mkUntypedMintingPolicy checkedMkMustUseOutputAsCollateralPolicy

mustUseOutputAsCollateralPolicy :: PSU.Language -> L.MintingPolicy
mustUseOutputAsCollateralPolicy = \case
  PSU.PlutusV1 -> mustUseOutputAsCollateralPolicyV1
  PSU.PlutusV2 -> mustUseOutputAsCollateralPolicyV2

mintingPolicy :: PSU.Language -> forall a. L.MintingPolicy -> Constraints.ScriptLookups a
mintingPolicy = \case
  PSU.PlutusV1 -> Constraints.plutusV1MintingPolicy
  PSU.PlutusV2 -> Constraints.plutusV2MintingPolicy

mintingPolicyHash :: PSU.Language -> L.MintingPolicy -> L.MintingPolicyHash
mintingPolicyHash = \case
  PSU.PlutusV1 -> PSU.V1.mintingPolicyHash
  PSU.PlutusV2 -> PSU.V2.mintingPolicyHash

type SubmitTx
  =  Constraints.ScriptLookups UnitTest
  -> Constraints.TxConstraints (Scripts.RedeemerType UnitTest) (Scripts.DatumType UnitTest)
  -> Contract () Empty ContractError Tx.CardanoTx

cardanoSubmitTx :: SubmitTx
cardanoSubmitTx lookups tx = let
  p = defaultCheckOptions ^. emulatorConfig . Trace.params
  in submitUnbalancedTx $ either (error . show) id $ Tx.Constraints.mkTx @UnitTest p lookups tx

ledgerSubmitTx :: SubmitTx
ledgerSubmitTx = submitTxConstraintsWith

mustUseOutputAsCollateralPolicyHash :: PSU.Language -> L.MintingPolicyHash
mustUseOutputAsCollateralPolicyHash lc = mintingPolicyHash lc $ mustUseOutputAsCollateralPolicy lc

mustUseOutputAsCollateralPolicyCurrencySymbol :: PSU.Language -> L.CurrencySymbol
mustUseOutputAsCollateralPolicyCurrencySymbol = Value.mpsSymbol . mustUseOutputAsCollateralPolicyHash
