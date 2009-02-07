{-# LANGUAGE ViewPatterns, FlexibleInstances, TypeSynonymInstances, NoMonomorphismRestriction, ExistentialQuantification, UndecidableInstances #-}
-- 2009.01.08
-- 2009.02.07
-- autumnae
--
-- The graph is made of nodes named/referenced by Int's.
-- Nodes have a field denoting their type, but otherwise
-- have all the same type (i.e. Node).
--
-- To gain some safety from Haskell's type system,
-- functions to create and combine nodes are typed :
-- nodes have the same type (so they can be put inside
-- a Map) but their reference are typed.
--
-- But nothing enforces the relationship between the type
-- of the typed references and the value denoting that type
-- inside the Node. See for instance how the Float type
-- appearing in the type signature of (constant float) is related
-- to the Float value (of type TypeRep) in the constructed
-- node. Maybe I could use TH to generate some of this stuff.
--
-- 'usage' : in ghci : doDot ex1
-- or : ghc Graph.hs -e 'doDot ex1' | dot -Tsvg -oex1.svg
--
module Graph where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.Maybe
import Data.List
import Data.Typeable
import Data.Dynamic

import Foreign.C.Types
import Foreign.Storable
import Foreign.Ptr
import Foreign.ForeignPtr

true = True
false = False

int = undefined :: CInt
float = undefined :: CFloat

-- Thanks to Ross Mellgren on the Haskell-Cafe mailing list.
argsOf :: TypeRep -> [TypeRep]
argsOf ty
  | typeRepTyCon ty == funTyCon = let ([x,y]) = typeRepArgs ty in x : argsOf y
  | otherwise = [ty] -- 'return' type
  where funTyCon :: TyCon
        funTyCon = mkTyCon "->"

myTypeOf :: Typeable a => a -> [TypeRep]
myTypeOf = argsOf . typeOf

instance Storable String where
  -- sizeOf :: a -> Int
  -- alignment :: a -> Int
  -- peekElemOff :: Ptr a -> Int -> IO a
  -- pokeElemOff :: Ptr a -> Int -> a -> IO ()
  -- peekByteOff :: Ptr b -> Int -> IO a
  -- pokeByteOff :: Ptr b -> Int -> a -> IO ()
  -- peek :: Ptr a -> IO a
  -- poke :: Ptr a -> a -> IO ()
  sizeOf = error "TODO : Storable String instance."
  alignment = error "TODO : Storable String instance."
  peekElemOff = error "TODO : Storable String instance."
  pokeElemOff = error "TODO : Storable String instance."
  peekByteOff = error "TODO : Storable String instance."
  pokeByteOff = error "TODO : Storable String instance."
  poke = error "TODO : Storable String instance."

----------------------------------------------------------------------
-- Node
----------------------------------------------------------------------

-- A reference is simply an Int. But to gain some type-safety
-- the reference are wrapped (below).
type Ref = Int

-- A typed reference.
data TRef a = TRef Ref
  deriving Show

type RInt = TRef Int
type RFloat = TRef Float

type Rank = Int

-- e.g. Op ([Int,Int],Int) "plus" [a,b] [c] means the node Plus depends
-- on a and b (the parents) and c depends on it (c is a child of Plus).
-- Furthermore the type of the parents should match with the one of the Op.
data Node = Cst Type  String [Ref]              -- children 
          | In  Type  String [Ref]              -- children
          | Out Type  String [Ref] Rank         -- parents
          | Op ([TypeRep], Type) String [Ref] [Ref] Rank -- parents, children
  deriving Show

isCst (Cst _ _ _) = True
isCst _ = False
isIn (In _ _ _) = True
isIn _ = False
isOut (Out _ _ _ _) = True
isOut _ = False
isOp (Op _ _ _ _ _) = True
isOp _ = False

info (Cst _ i _) = i
info (In _ i _) = i
info (Out _ i _ _) = i
info (Op _ i _ _ _) = i

rank :: Node -> Rank
rank (Cst _ _ _) = 0
rank (In _ _ _) = 0
rank (Out _ _ _ rk) = rk
rank (Op _ _ _ _ rk) = rk

parents (Cst _ _ _) = []
parents (In _ _ _) = []
parents (Out _ _ p _) = p
parents (Op _ _ p _ _) = p

children (Cst _ _ c) = c
children (In _ _ c) = c
children (Out _ _ _ _) = []
children (Op _ _ _ c _) = c

typ (Cst t _ _) = t
typ (In t _ _) = t
typ (Out t _ _ _) = t
typ (Op (_,t) _ _ _ _) = t

setChildren (Cst t i c)    c' = Cst t i c'
setChildren (In t i c)     c' = In t i c'
setChildren (Out t i p r)  _  = Out t i p r
setChildren (Op t i p c r) c' = Op t i p c' r

setParents (Cst t i c)    _  = Cst t i c
setParents (In t i c)     _  = In t i c
setParents (Out t i p r)  p' = Out t i p' r
setParents (Op t i p c r) p' = Op t i p' c r

----------------------------------------------------------------------
-- Graph
----------------------------------------------------------------------

data G = G { nodes :: IM.IntMap Node, nextName :: Ref }
  deriving Show

type N a = State G (TRef a)

emptyGraph = G IM.empty 0

graph :: State G a -> IM.IntMap Node
graph = nodes . (flip execState emptyGraph)

alist = IM.toList

-- Returns all the nodes sorted by their rank (so Inputs and Constants come first).
byrank = sortByRank . alist
sortByRank = sortBy (\a b -> (rank . snd) a `compare` (rank . snd) b)

-- Groups all the nodes according to their rank (with Inputs and
-- Constants coming first).
grouped g = groupBy (\a b -> (rank . snd) a == (rank . snd) b) (byrank g)

-- Gives the list of node which depends on the node (referenced by r).
below g r = tail $ below' r
  where below' r = let n = l r in (r,n) : concatMap below' (children n)
        l r = g IM.! r

----------------------------------------------------------------------
-- Dot
----------------------------------------------------------------------

-- nodes
dotOne1 (r,node) = "n" ++ show r ++ " [" ++
  (concat $ intersperse ", " $ ["label=\"" ++ info node ++ "\""] ++ attr node)
  ++ "]\n"
  where attr n | isCst n = ["color=grey"]
               | isIn n = ["color=cyan"]
               | isOut n = ["color=orange"]
               | otherwise = []
dotRank1 = concatMap dotOne1
dot1 = (concatMap dotRank1) . grouped

-- arcs
dotOne2 (r,node) = concatMap (\c -> "n" ++ show r ++ " -> n" ++ show c ++ "\n") (children node)
dotRank2 = concatMap dotOne2
dot2 = (concatMap dotRank2) . grouped

doDot g = do
  let g' = graph g
  putStrLn "digraph G {"
  putStr $ dot1 g'
  putStrLn ""
  putStr $ dot2 g'
  putStrLn "}"

----------------------------------------------------------------------
-- C
----------------------------------------------------------------------

vars g = map var (byrank g)
var (r,node) = (cshow . typ) node ++ " " ++ cname (r,node) ++ ";" ++ " /* " ++ info node ++ " */"
cshow t | t == Type int = "int"
cname (r,(Cst _ _ _)) = "cst" ++ show r
cname (r,(In _ _ _)) = "inp" ++ show r
cname (r,(Op _ _ _ _ _)) = "nod" ++ show r
cname (r,(Out _ _ _ _)) = "out" ++ show r

ups1 g = map up1 inputs
  where inputs = takeWhile (isIn . snd) (byrank g)
up1 (r,node) = "void up" ++ show r ++ " ();\n"
  ++ "void up_" ++ info node ++ " (" ++ (cshow . typ) node ++ " x" ++ ")\n{\n"
  ++ cname (r,node) ++ " = x;\n"
  ++ "up" ++ show r ++ " ();\n"
  ++ "}\n"

ups2 g = map (up2 g) inputs
  where inputs = takeWhile (isIn . snd) (byrank g)
up2 g (r,node) = "void up" ++ show r ++ " ()\n{\n" ++ body (r,node) g ++ "\n}"
body (r,node) g = concatMap (upNode g) depends
  where depends = sortByRank $ below g r
upNode g (r,node) | isOut node = "" -- no data to update for an output node
                  | isIn  node = error "input node shouldn't be updated from here"
                  | isCst node = "" -- no update for a constant node
                  | isOp  node = upOp g (r,node)
upOp g (r,node@(Op ts info ps cs rk)) = upOp' g (r,node)
upOp' g (r,node@(Op (ts,_) "+" [a,b] _ _)) | ts == [typeOf int, typeOf int, typeOf int] =
  cname (r,node) ++ " = " ++ cname (a,g IM.! a) ++ " + " ++ cname (b,g IM.! b) ++ ";"

outs g = concatMap outOne funs
  where outputs = filter (isOut . snd) (alist g)
        funs = map (info . snd) $ nubBy (\(_,node1) (_,node2) -> info node1 == info node2) outputs
        outOne name = "void out_" ++ name ++ " ()\n{\n" ++ body name ++ "\n}"
        body name = concatMap call $ filter ((== name) . info . snd) outputs
        call (r,node) = info node ++ " (" ++ cname (r,node) ++ ");"

doCode g = do
  let g' = graph g
  putStrLn $ unlines $ vars g'
  putStrLn $ unlines $ ups1 g'
  putStrLn $ unlines $ ups2 g'
  putStrLn $ outs g'

----------------------------------------------------------------------
-- Storable
----------------------------------------------------------------------

class (Storable p, Typeable p) => Pointable p where
  ptr :: Ptr p

instance (Storable p, Typeable p) => Pointable p where
  ptr = nullPtr

data Type = forall a . Pointable a => Type a

instance Show Type where
  show (Type a) = show (typeOf a)

instance Eq Type where
  (Type a) == (Type b)= (typeOf a) == (typeOf b)

mySizeOf (Type a) = sizeOf a
myAlignment (Type a) = alignment a

data Memory = Memory Int (IM.IntMap Node)
  deriving Show

-- Describe the graph as its data would be laid-off in a C struct :
-- the size and a mapping with byte offset (respecting alignment)
-- of the nodes.
memory [] = Memory 0 IM.empty
memory xs = Memory size (IM.fromList $ map snd mem)
  where (size,mem) = mapAccumL (memoryAcc mem) 0 xs
memoryAcc mem off x@(r,node) =
  if re == 0 -- test if already aligned
    then (sx + off,      (r,(off,     n')))
    else (sx + off + al, (r,(off + al,n')))
  where tx = typ $ snd x
        sx = mySizeOf tx
        ax = myAlignment tx
        re = off `mod` ax -- how much is needed if any
        al = ax - re      -- padding to regain alignment if needed
        n  = setChildren node $ map (offset mem) (children node)
        n' = setParents n $ map (offset mem) (parents n)

-- translate from the map-ref (or alist-ref) to the memory-ref.
offset mem r = fst . fromJust $ lookup r mem

go (Memory size m) = do
  mem <- mallocForeignPtrBytes size
  return ()

----------------------------------------------------------------------
-- Graph
----------------------------------------------------------------------

instance Show (State G a) where
  show g = show $ execState g emptyGraph

instance Eq (N w) where
-- TODO special case for commutative operations.
  a == b = same g1 g2 (n1,n2)
   where
    (TRef n1, nodes -> g1) = runState a emptyGraph
    (TRef n2, nodes -> g2) = runState b emptyGraph

eq a b = same g1 g2 (n1,n2)
   where
    (TRef n1, nodes -> g1) = runState a emptyGraph
    (TRef n2, nodes -> g2) = runState b emptyGraph

same g1 g2 (n1,n2) =
  case (g1 IM.! n1) of
    Cst t1 i1 _     -> case (g2 IM.! n2) of
                         Cst t2 i2 _ -> t1 == t2 && i1 == i2
                         otherwise   -> False
    In t1 i1 _      -> case (g2 IM.! n2) of
                         In t2 i2 _ -> t1 == t2 && i1 == i2
                         otherwise   -> False
    Out t1 i1 p1 _  -> case (g2 IM.! n2) of
                         Out t2 i2 p2 _ -> t1 == t2 && i1 == i2 && length p1 == length p2 && and (map (same g1 g2) (zip p1 p2))
                         otherwise   -> False
    Op t1 i1 p1 _ _ -> case (g2 IM.! n2) of
                         Op t2 i2 p2 _ _ -> t1 == t2 && i1 == i2 && length p1 == length p2 && and (map (same g1 g2) (zip p1 p2))
                         otherwise       -> False

instance (Pointable n, Num n) => Num (N n) where
  (+) = lift2 (+) "+"
  (*) = lift2 (*) "*"
  signum = lift1 signum "signumf"
  abs = lift1 abs "abs"
  fromInteger = (constant undefined) . show

instance (Pointable n, Fractional n) => Fractional (N n) where
  (/) = lift2 (/) "/"
  recip = lift1 recip "recip"
  fromRational = (constant undefined) . show . fromRational

addChild' c n@(Cst t info cs) = if c `elem` cs then n else Cst t info (c:cs)
addChild' c n@(In t info cs) = if c `elem` cs then n else In t info (c:cs)
addChild' c n@(Op t info ps cs rk) = if c `elem` cs then n else Op t info ps (c:cs) rk

-- Create a node (and give it automatically a name).
mkNode n = do
  i <- gets nextName
  ns <- gets nodes
  put $ G { nodes = IM.insert i n ns, nextName = i + 1 }
  return i

-- Add c as a child to the node n.
addChild c n = do
  ns <- gets nodes
  g <- get
  put $ g { nodes = IM.adjust (addChild' c) n ns }

constant :: (Pointable a) => a -> String -> N a
constant v info = mkNode (Cst (Type v) info []) >>= return . TRef

input :: (Pointable a) => a -> String -> N a
input v info = mkNode (In (Type v) info []) >>= return . TRef

output info a = do
  TRef n1 <- a
  node <- gets ((IM.! n1) . nodes)
  n <- mkNode (Out (typ node) info [n1] (rank node + 1))
  addChild n n1
  return (TRef n)

out info (TRef n1) = do
  node <- gets ((IM.! n1) . nodes)
  n <- mkNode (Out (typ node) info [n1] (rank node + 1))
  addChild n n1
  return (TRef n)

lift1 :: (Pointable a, Pointable b) => (a -> b) -> String -> (N a -> N b)
lift1 f name = \a -> do
  r1 <- a
  op1 f name r1

-- test for similar subgraph (not every nodes are checked, just the two
-- added nodes are tested against each other, but it works).
lift2' :: (Pointable a, Pointable b, Pointable c) => (a -> b -> c) -> String -> (N a -> N b -> N c)
lift2' f name = \a b ->
  if a `eq` b
   then do
    TRef n1 <- a
    rk1 <- gets (rank . (IM.! n1) . nodes)
    n <- mkNode (Op (init $ myTypeOf f,Type $ f undefined undefined) name [n1,n1] [] (rk1 + 1))
    addChild n n1
    return (TRef n)
   else do
    r1 <- a
    r2 <- b
    op2 f name r1 r2
-- no test
lift2 :: (Pointable a, Pointable b, Pointable c) => (a -> b -> c) -> String -> (N a -> N b -> N c)
lift2 f name = \a b -> do
  r1 <- a
  r2 <- b
  op2 f name r1 r2

op1 :: (Pointable a, Pointable b) => (a -> b) -> String -> TRef a -> N b
op1 f name (TRef n1) = do
  rk1 <- gets (rank . (IM.! n1) . nodes)
  n <- mkNode (Op (init $ myTypeOf f,Type $ f undefined) name [n1] [] (rk1 + 1))
  addChild n n1
  return (TRef n)

op2 :: (Pointable a, Pointable b, Pointable c) => (a -> b -> c) -> String -> TRef a -> TRef b -> N c
op2 f name (TRef n1) (TRef n2) = do
  rk1 <- gets (rank . (IM.! n1) . nodes)
  rk2 <- gets (rank . (IM.! n2) . nodes)
  n <- mkNode (Op (init $ myTypeOf f,Type $ f undefined undefined) name [n1,n2] [] (max rk1 rk2 + 1))
  addChild n n1
  addChild n n2
  return (TRef n)

add = op2 (+) "+"

----------------------------------------------------------------------
-- Examples
----------------------------------------------------------------------

foo = lift2 f "foo"
f :: CInt -> CFloat -> String
f x s = "hello"

milliseconds = input int "milliseconds"

ex1 = output "hey" $ (milliseconds + 45) `foo` (55.6 * 1.2)

ex1' = execState ex1 emptyGraph

-- The main problem of this approch is showed
-- by doDot ex2 : the subgraph constructed by a
-- is not shared. (It's just like a is a little
-- program that is run twice by the + combinator.)
-- If it was a real little language, a would be a
-- lookup on a symbol table, not two 'commands'.
--
-- A solution is to add a node to the graph if
-- there isn't yet such a node. I.e. every new node
-- is checked against every existing node. Maybe it
-- would be expensive but it could find redondant
-- node even if they were not initially shared.
ex2 = output "yah" $ a + a
  where a = (milliseconds + 12 + 46)
(+++) = lift2' (+) "+check"
ex3 = output "yah-shared" $ a +++ a
  where a = (milliseconds + 12 + 46)

-- no problem to discover sharing here but more ugly syntax.
ex4 = do
  m <- milliseconds
  a <- add m m
  out "console" a
  return ()
