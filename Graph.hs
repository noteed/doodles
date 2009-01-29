{-# LANGUAGE ViewPatterns, FlexibleInstances #-}
-- 2009.01.08
-- 2009.01.27
-- autumnae
--
-- The graph is made of nodes named/referenced by Int's.
-- Nodes have a field denoting their type, but otherwise
-- have all the same type (i.e. Node).
-- To gain some safety from Haskell's type system,
-- function to create and combine nodes are typed.
-- But nothing enforces the relationship between the type
-- of the typed references and the value denoting that type
-- inside the Node. See for instance how the Float type
-- appearing in the type signature of baseInt is related
-- to the Float value (of type NodeType) in the constructed
-- node. Maybe I could use TH to generate some of this stuff.
--
--
module Graph where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.List
import Data.Typeable

true = True
false = False

-- Possible type value for a node. It should match the
-- type of the reference.
data NodeType = Int | Float
  deriving Show

-- A reference is simply an Int. But to gain some type-safety
-- the reference are wrapped (below).
type Ref = Int

-- A class is provided to get the untypeded reference and
-- wrap it. Also, to give the value representing the type.
class WrapRef w where
  unwrapRef :: w -> Ref
  wrapRef :: Ref -> w

data RInt = RInt Ref

instance WrapRef RInt where
  unwrapRef (RInt n) = n
  wrapRef n = RInt n

data RFloat = RFloat Ref

instance WrapRef RFloat where
  unwrapRef (RFloat n) = n
  wrapRef n = RFloat n

type Rank = Int

-- e.g. Op Int "plus" [a,b] [c] means the node Plus depends on a and b (the parents)
-- and c depends on it (c is a child of Plus).
data Node = Base NodeType String [Ref]
          | Op NodeType String  [Ref] [Ref] Rank -- parents, children
  deriving Show

info (Base _ i _) = i
info (Op _ i _ _ _) = i

rank :: Node -> Rank
rank (Base _ _ _) = 0
rank (Op _ _ _ _ rk) = rk

parents (Base _ _ _) = []
parents (Op _ _ _ p _) = p

children (Base _ _ c) = c
children (Op _ _ _ c _) = c

data G = G { nodes :: IM.IntMap Node, nextName :: Ref }
  deriving Show

emptyGraph = G IM.empty 0

graph :: State G a -> IM.IntMap Node
graph = nodes . (flip execState emptyGraph)

alist = IM.toList . graph

byrank g = sortBy (\a b -> (rank . snd) a `compare` (rank . snd) b) (alist g)

grouped g = groupBy (\a b -> (rank . snd) a == (rank . snd) b) (byrank g)

-- lables
dotOne1 (r,node) = "n" ++ show r ++ " [label=\"" ++ info node ++ "\"]\n"
dotRank1 = concatMap dotOne1
dot1 = (concatMap dotRank1) . grouped

-- arcs
dotOne2 (r,node) = concatMap (\c -> "n" ++ show r ++ " -> n" ++ show c ++ "\n") (children node)
dotRank2 = concatMap dotOne2
dot2 = (concatMap dotRank2) . grouped

doDot g = do
  putStrLn "digraph G {"
  putStr $ dot1 g
  putStrLn ""
  putStr $ dot2 g
  putStrLn "}"

instance WrapRef w => Show (State G w) where
--  show g = show (ns IM.! i)
--    where (unwrapRef -> i,nodes -> ns) = runState g emptyGraph
  show g = show $ execState g emptyGraph

instance WrapRef w => Eq (State G w) where
  a == b = error "TODO: Eq instance for WrapRef."

instance Num (State G RInt) where
  (+) = nAdd
  (*) = nMul
  signum = nSignum
  abs = nAbs
  fromInteger = baseInt . show

instance Num (State G RFloat) where
  (+) = nAddF
  (*) = nMulF
  signum = nSignumF
  abs = nAbsF
  fromInteger =  baseFloat . show . fromInteger

instance Fractional (State G RFloat) where
  (/) = nDivF
  recip = nRecipF
  fromRational = baseFloat . show . fromRational


addChild' c (Base t info cs) = Base t info (c:cs)
addChild' c (Op t info ps cs rk) = Op t info ps (c:cs) rk

-- Create a node (and give it automatically a name).
mkNode n = do
  i <- gets nextName
  ns <- gets nodes
  put $ G { nodes = IM.insert i n ns, nextName = i + 1 }
  return i

-- Add a node named (refenced by) i.
addNode i n = do
  ns <- gets nodes
  put $ G { nodes = IM.insert i n ns, nextName = i + 1 }

-- Add c as a child to the node n.
addChild c n = do
  ns <- gets nodes
  g <- get
  put $ g { nodes = IM.adjust (addChild' c) n ns }

baseInt :: String -> State G RInt
baseInt info = mkNode (Base Int info []) >>= return . wrapRef

baseFloat :: String -> State G RFloat
baseFloat info = mkNode (Base Float info []) >>= return . wrapRef

unOp :: String -> State G RInt -> State G RInt
unOp name a = do
  (unwrapRef -> n1) <- a
  rk <- gets (rank . (IM.! n1) . nodes)
  n <- gets nextName
  addChild n n1
  addNode n (Op Int name [n1] [] (rk + 1))
  return (wrapRef n)

binOp :: String -> State G RInt -> State G RInt -> State G RInt
binOp name a b = do
  (unwrapRef -> n1) <- a
  (unwrapRef -> n2) <- b
  rk1 <- gets (rank . (IM.! n1) . nodes)
  rk2 <- gets (rank . (IM.! n2) . nodes)
  n <- gets nextName
  addChild n n1
  addChild n n2
  addNode n (Op Int name [n1,n2] [] (max rk1 rk2 + 1))
  return (wrapRef n)

unOpF :: String -> State G RFloat -> State G RFloat
unOpF name a = do
  (unwrapRef -> n1) <- a
  rk <- gets (rank . (IM.! n1) . nodes)
  n <- gets nextName
  addChild n n1
  addNode n (Op Float name [n1] [] (rk + 1))
  return (wrapRef n)

binOpF :: String -> State G RFloat -> State G RFloat -> State G RFloat
binOpF name a b = do
  (unwrapRef -> n1) <- a
  (unwrapRef -> n2) <- b
  rk1 <- gets (rank . (IM.! n1) . nodes)
  rk2 <- gets (rank . (IM.! n2) . nodes)
  n <- gets nextName
  addChild n n1
  addChild n n2
  addNode n (Op Float name [n1,n2] [] (max rk1 rk2 + 1))
  return (wrapRef n)

nAdd, nMul :: State G RInt -> State G RInt -> State G RInt
nAdd = binOp "add"
nMul = binOp "mul"
nAbs = unOp "abs"
nSignum = unOp "signum"

nAddF = binOpF "addf"
nMulF = binOpF "mulf"
nAbsF = unOpF "absf"
nSignumF = unOpF "signumf"
nDivF = binOpF "divf"
nRecipF = unOpF "recipf"

foo :: State G RInt -> State G RFloat -> State G RFloat
foo x s = do
  (unwrapRef -> n1) <- x
  (unwrapRef -> n2) <- s
  rk1 <- gets (rank . (IM.! n1) . nodes)
  rk2 <- gets (rank . (IM.! n2) . nodes)
  n <- gets nextName
  addChild n n1
  addChild n n2
  addNode n (Op Float "foo" [n1,n2] [] (max rk1 rk2 + 1))
  return (wrapRef n)

milliseconds = baseInt "milliseconds"

ex1 = (milliseconds + 45) `foo` 55.6

ex1' = execState ex1 emptyGraph


