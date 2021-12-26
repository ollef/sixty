{-# LANGUAGE ScopedTypeVariables #-}

module Assembly.HeapAllocates where

import qualified Assembly
import Control.Exception.Lifted
import Control.Monad.Trans.Maybe
import Data.Some
import Monad
import Protolude hiding (try)
import Query (Query)
import qualified Query
import Rock

type HeapAllocates = MaybeT M ()

run :: HeapAllocates -> M Bool
run ha = do
  result <- runMaybeT ha
  pure $ case result of
    Nothing -> True
    Just () -> False

heapAllocates :: HeapAllocates
heapAllocates = MaybeT $ pure Nothing

doesn'tHeapAllocate :: HeapAllocates
doesn'tHeapAllocate = pure ()

definitionHeapAllocates :: Assembly.Definition -> HeapAllocates
definitionHeapAllocates definition =
  case definition of
    Assembly.KnownConstantDefinition {} -> doesn'tHeapAllocate
    Assembly.ConstantDefinition _ _ _ basicBlock -> basicBlockHeapAllocates basicBlock
    Assembly.FunctionDefinition _ _ basicBlock -> basicBlockHeapAllocates basicBlock

basicBlockHeapAllocates :: Assembly.BasicBlock -> HeapAllocates
basicBlockHeapAllocates (Assembly.BasicBlock instructions _return) = mapM_ instructionHeapAllocates instructions

instructionHeapAllocates :: Assembly.Instruction -> HeapAllocates
instructionHeapAllocates instruction =
  case instruction of
    Assembly.Copy {} -> doesn'tHeapAllocate
    Assembly.Call _ fun _ ->
      case fun of
        Assembly.LocalOperand {} -> heapAllocates
        Assembly.GlobalConstant {} -> heapAllocates
        Assembly.GlobalFunction funName _ _ -> do
          result <- try $ fetch $ Query.HeapAllocates funName
          case result of
            Left (Cyclic (_ :: Some Query)) -> doesn'tHeapAllocate
            Right True -> heapAllocates
            Right False -> doesn'tHeapAllocate
        Assembly.StructOperand {} -> heapAllocates
        Assembly.Lit {} -> heapAllocates
    Assembly.Load {} -> doesn'tHeapAllocate
    Assembly.Store {} -> doesn'tHeapAllocate
    Assembly.InitGlobal {} -> doesn'tHeapAllocate
    Assembly.Add {} -> doesn'tHeapAllocate
    Assembly.Sub {} -> doesn'tHeapAllocate
    Assembly.Mul {} -> doesn'tHeapAllocate
    Assembly.AddPointer {} -> doesn'tHeapAllocate
    Assembly.StackAllocate {} -> doesn'tHeapAllocate
    Assembly.SaveStack {} -> doesn'tHeapAllocate
    Assembly.RestoreStack {} -> doesn'tHeapAllocate
    Assembly.HeapAllocate {} -> heapAllocates
    Assembly.ExtractHeapPointer {} -> doesn'tHeapAllocate
    Assembly.ExtractHeapPointerConstructorTag {} -> doesn'tHeapAllocate
    Assembly.ExtractValue {} -> doesn'tHeapAllocate
    Assembly.Switch _ _ branches default_ -> do
      mapM_ (basicBlockHeapAllocates . snd) branches
      basicBlockHeapAllocates default_
