{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
 
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
 
 
import           Control.Monad        hiding (fmap)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.List.NonEmpty   (NonEmpty (..))
import           Data.Map             as Map
import           Data.Text            (pack, Text)
import           GHC.Generics         (Generic)
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Scripts       as Scripts
import qualified Ledger.Typed.Scripts as Scripts hiding (validatorHash, Validator)
import           Ledger.Value         as Value
import           Ledger.Ada           as Ada
import           Playground.Contract  (ensureKnownCurrencies, printSchemas, stage, printJson, BlockchainActions)
import           Playground.Contract  as Contract

import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (IO, Semigroup (..), Show (..), String)
import           Schema               (ToSchema)
import           Text.Printf          (printf)
import           Language.PlutusTx.Prelude            hiding (Applicative (..), Semigroup (..), until)
import qualified Language.PlutusTx                    as PlutusTx
import qualified Ledger.Contexts                      as V
import           Language.Plutus.Contract (logInfo, HasTxConfirmation, submitTxConstraints, awaitTxConfirmed, HasOwnPubKey, HasWriteTx, submitTxConstraintsWith, HasUtxoAt,throwError, select )

 
 
 
data LendingPool = LendingPool
   { lPricePerToken   :: !Integer
   , lCurrency :: !CurrencySymbol
   , lToken    :: !TokenName
   , lPercent :: !Integer
   } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)
 
instance Eq LendingPool where
   {-# INLINABLE (==) #-}
   a == b = (lPricePerToken   a == lPricePerToken   b) &&
            (lCurrency a == lCurrency b) &&
            (lToken    a == lToken    b) &&
            (lPercent a == lPercent b)
 
PlutusTx.makeIsData ''LendingPool
PlutusTx.makeLift ''LendingPool
 
data Lend = Lend
   { lLender :: !PubKeyHash
   , lLendAmount    :: !Integer
   } deriving Show
 
instance Eq Lend where
   {-# INLINABLE (==) #-}
   b == c = (lLender b == lLender c) &&
            (lLendAmount b == lLendAmount c)
 
PlutusTx.makeIsData ''Lend
PlutusTx.makeLift ''Lend
 
data Borrow = Borrow
   { bBorrower :: !PubKeyHash
   , bBorrowToken  :: !Integer
   } deriving Show
 
instance Eq Borrow where
   {-# INLINABLE (==) #-}
   b == c = (bBorrower b == bBorrower c) &&
            (bBorrowToken b == bBorrowToken c)
 
PlutusTx.makeIsData ''Borrow
PlutusTx.makeLift ''Borrow
 
 
data LendAction = MkLend Lend | MkBorrow Borrow | CloseBorrow | CloseLend
   deriving Show
 
PlutusTx.makeIsData ''LendAction
PlutusTx.makeLift ''LendAction
 
data LendDatum = LendDatum
   { ldLendingPool   :: !LendingPool
   , ldLenders:: !(Maybe[Lend])
   , ldBorrowers :: !(Maybe[Borrow])
   , ldAmountAda :: !(Maybe Integer)
   , ldAmountToken :: !(Maybe Integer)
   } deriving Show
 
PlutusTx.makeIsData ''LendDatum
PlutusTx.makeLift ''LendDatum
 
data Lending
instance Scripts.ScriptType Lending where
   type instance RedeemerType Lending = LendAction
   type instance DatumType Lending = LendDatum
 
{-# INLINABLE countAda #-}
countAda :: LendDatum -> Integer
countAda LendDatum{..} = case ldAmountAda of
   Nothing      -> 0
   Just a       -> a

countToken :: LendDatum -> Integer 
countToken LendDatum{..} = case ldAmountToken of
   Nothing      -> 0
   Just a       -> a

tokenDatum :: LendDatum -> TokenName 
tokenDatum LendDatum{..} = lToken ldLendingPool 


currencyDatum :: LendDatum -> CurrencySymbol 
currencyDatum LendDatum{..} = lCurrency ldLendingPool 

countValue :: LendDatum -> Value
countValue d = Value.singleton (currencyDatum  d) (tokenDatum d) (countToken d) <> Ada.lovelaceValueOf (countAda d)
    
{-# INLINABLE mkLendingPoolValidator #-}
mkLendingPoolValidator :: LendDatum -> LendAction -> ValidatorCtx -> Bool
mkLendingPoolValidator ld redeemer ctx =
   traceIfFalse "wrong input value" correctInputValue &&
   case redeemer of
       MkLend l@Lend{..} -> True -- need  add
       CloseLend -> True
       MkBorrow b@Borrow{..} -> True
       CloseBorrow -> True
 
 where
   --info :: TxInfo
   --info = scriptContextTxInfo ctx
 
   input :: TxInInfo
   input = findOwnInput ctx
 
   inVal :: Value
   inVal = txInInfoValue input
 
   lendingPool :: LendingPool
   lendingPool = ldLendingPool ld
 
   amountAda :: Integer
   amountAda  = case (ldAmountAda ld) of
       Nothing      -> 0
       Just a       -> a
  
   amountToken :: Integer
   amountToken = case (ldAmountToken ld) of
       Nothing      -> 0
       Just a       -> a
  
   tokenValue :: Value
   tokenValue = Value.singleton (lCurrency lendingPool) (lToken lendingPool) amountToken
 
   adaValue :: Value
   adaValue = Ada.lovelaceValueOf amountAda
 
   correctInputValue :: Bool
   correctInputValue = inVal == (tokenValue <> adaValue)
 
lendingTypedValidator :: Scripts.ScriptInstance Lending
lendingTypedValidator = Scripts.validator @Lending
   $$(PlutusTx.compile [|| mkLendingPoolValidator ||])
   $$(PlutusTx.compile [|| wrap ||])
 where
   wrap = Scripts.wrapValidator @LendDatum @LendAction
 
lendingValidator :: Validator
lendingValidator = Scripts.validatorScript lendingTypedValidator
 
lendingHash :: Ledger.ValidatorHash
lendingHash = Scripts.validatorHash lendingValidator

lendingAddress :: Ledger.Address
lendingAddress = ScriptAddress lendingHash
 
data StartLendParams = StartLendParams
    { slNumAda   :: !Integer
    , slCurrency :: !CurrencySymbol
    , slToken    :: !TokenName
    } deriving (Generic, ToJSON, FromJSON, ToSchema)
 
data CreateLendingPoolParams = CreateLendingPoolParams
   { cpPricePerToken   :: !Integer
   , cpCurrency :: !CurrencySymbol
   , cpToken    :: !TokenName
   , cpPercent :: !Integer
   } deriving (Generic, ToJSON, FromJSON, ToSchema)
 
data StartBorrowParams = StartBorrowParams
    { sbNumToken :: !Integer
    , sbCurrency :: !CurrencySymbol
    , sbToken    :: !TokenName
    } deriving (Generic, ToJSON, FromJSON, ToSchema)
 

type LendingPoolSchema =
    BlockchainActions
        Contract..\/ Endpoint "create" CreateLendingPoolParams
        Contract..\/ Endpoint "startlend" StartLendParams
 
createLendingPool :: ( HasTxConfirmation s, HasOwnPubKey s, HasWriteTx s, HasUtxoAt s) => CreateLendingPoolParams -> Contract s Text ()
createLendingPool CreateLendingPoolParams{..} = 
    do
        logInfo @String $ printf "ahihi"
        lender <- pubKeyHash <$> ownPubKey

        let l = LendingPool
                { lPricePerToken   = cpPricePerToken
                , lCurrency        = cpCurrency
                , lToken           = cpToken
                , lPercent         = cpPercent
                }
            d = LendDatum
                { ldLendingPool   = l
                , ldLenders       = Just [Lend {lLender = lender, lLendAmount = 1}]
                , ldBorrowers     = Nothing
                , ldAmountAda     = Just 1
                , ldAmountToken   = Just 1
                }
            v = countValue d
            tx = mustPayToTheScript d v
        ledgerTx <- submitTxConstraints lendingTypedValidator tx
        void $ awaitTxConfirmed $ txId ledgerTx
        logInfo @String $ printf "started lending pool %s" (show l)



startLend :: ( HasTxConfirmation s, HasOwnPubKey s, HasWriteTx s, HasUtxoAt s) => StartLendParams -> Contract s Text ()
startLend StartLendParams{..} =
    do
        lender <- pubKeyHash <$> ownPubKey
        (oref, o, d@LendDatum{..}) <- findLendingPool slCurrency slToken
        logInfo @String $ printf "made lender %s" (show d)                             

        pkh <- pubKeyHash <$> ownPubKey
        let
            l  = Lend { lLender = pkh, lLendAmount = slNumAda }
            d' = addLender d pkh slNumAda 
            v  = countValue d'
            r  = Redeemer $ PlutusTx.toData $ MkLend l
            lookups = Constraints.scriptInstanceLookups lendingTypedValidator <>
                      Constraints.otherScript lendingValidator                <>
                      Constraints.unspentOutputs (Map.singleton oref o)
            tx      =   mustPayToTheScript d' v <> mustSpendScriptOutput oref r
        ledgerTx <- submitTxConstraintsWith lookups tx
        void $ awaitTxConfirmed $ txId ledgerTx
        logInfo @String $ printf "made lender %s" (show l) 


addLender :: LendDatum -> PubKeyHash -> Integer -> LendDatum
addLender d@LendDatum{..} pkh amount =
    let 
        ldAmountAda' = case ldAmountAda of 
                                Nothing -> Just amount
                                Just a  -> Just $ a + amount
        ldLenders' = case ldLenders of
                                Nothing -> Just [Lend {lLender = pkh, lLendAmount = amount}]
                                Just a  -> Just $ a <> [Lend {lLender = pkh, lLendAmount = amount}]
    in
        d { ldAmountAda = ldAmountAda', ldLenders = ldLenders'}
    

findLendingPool ::(HasTxConfirmation s, HasOwnPubKey s, HasWriteTx s,  HasUtxoAt s)
                => CurrencySymbol
                -> TokenName
                -> Contract s Text (TxOutRef, TxOutTx, LendDatum)
findLendingPool cs tn = do
    utxos <- utxoAt $ ScriptAddress lendingHash
    let xs = [ (oref, o)
             | (oref, o) <- Map.toList utxos
             , Value.valueOf (txOutValue $ txOutTxOut o) cs tn >= 0
             ]
    case xs of
        [(oref, o)] -> case txOutType $ txOutTxOut o of
            PayToPubKey   -> throwError "unexpected out type"
            PayToScript h -> case Map.lookup h $ txData $ txOutTxTx o of
                Nothing        -> throwError "datum not found"
                Just (Datum e) -> case PlutusTx.fromData e of
                    Nothing -> throwError "datum has wrong type"
                    Just d@LendDatum{..}
                        | lCurrency ldLendingPool == cs && lToken ldLendingPool == tn -> return (oref, o, d)
                        | otherwise                                           -> throwError "lending pool token missmatch"
        _           -> throwError "lending pool utxo not found"

endpoints :: Contract LendingPoolSchema Text ()
endpoints = (createLendingPool' `select` startLend')  >> endpoints
  where
    createLendingPool' = endpoint @"create"  >>= createLendingPool
    startLend' = endpoint @"startlend"  >>= startLend



mkSchemaDefinitions ''LendingPoolSchema

myToken :: KnownCurrency
myToken = KnownCurrency (ValidatorHash "f") "Token" (TokenName "T" :| [])

mkKnownCurrencies ['myToken]