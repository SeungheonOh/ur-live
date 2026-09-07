{-# LANGUAGE DerivingStrategies #-}

-- | Small semantic enums shared by the target-independent middle-end IRs.
module Vr.Middle
  ( FailureMode (..)
  , Effect (..)
  , ExportKind (..)
  , Sidedness (..)
  , DbMode (..)
  ) where

data FailureMode = FailureError | FailureNone
  deriving stock (Eq, Ord, Show)

data Effect = ReadOnly | ReadCookieWrite | ReadWrite
  deriving stock (Eq, Ord, Show)

data ExportKind
  = Link !Effect
  | Action !Effect
  | Rpc !Effect
  | Extern !Effect
  deriving stock (Eq, Ord, Show)

data Sidedness
  = PlacementPending
  | ServerOnly
  | ServerAndPull
  | ServerAndPullAndPush
  deriving stock (Eq, Ord, Show)

data DbMode = DbModePending | NoDb | OneQuery | AnyDb
  deriving stock (Eq, Ord, Show)
