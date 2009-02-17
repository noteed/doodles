{-# LANGUAGE ViewPatterns, FlexibleInstances, TypeSynonymInstances, NoMonomorphismRestriction, ExistentialQuantification, UndecidableInstances #-}
-- 2009.01.08
-- 2009.02.15
-- Vo Minh Thu
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
-- 'usage' : in ghci : dotString ex1
-- or : ghc Graph.hs -e 'putStrLn $ dotString ex1' | dot -Tsvg -oex1.svg
-- or : ghc -e "putStrLn $ cCodeString ex4" Graph.hs
-- or : ghc -e "ttcCode $ cCodeString ex4" Graph.hs
--
module Graph where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.Maybe
import Data.List

import Foreign.C.Types
import Foreign.Storable
import Foreign.Ptr
import Foreign.ForeignPtr

import Language.TCC
import Foreign.C.String

true = True
false = False

int = undefined :: CInt
float = undefined :: CFloat

-- Types handled by the graph
data TypeDepiction = TDInt
                   | TDFloat
                   | TDString
                   | TDVoid
  deriving (Eq, Ord, Show)

data InitialValue = IVInt CInt
                  | IVFloat CFloat
                  | IVString String
                  | IVVoid
                  | IVNone
  deriving (Eq, Ord, Show)

g :: CInt -> CInt -> CInt
g = (+)
g' a b = g (value a) (value b)

class IsInitialValue a => IsType a where
  typeDepiction :: a -> TypeDepiction

class IsInitialValue a where
  initialValue :: a -> InitialValue
  value :: InitialValue -> a

instance IsType CInt where
  typeDepiction _ = TDInt

instance IsType CFloat where
  typeDepiction _ = TDFloat

instance IsType String where
  typeDepiction _ = TDString

instance IsType () where
  typeDepiction _ = TDVoid

instance IsInitialValue CInt where
  initialValue a = IVInt a
  value (IVInt a) = a
  value a = error $ "Attempt to extract the value of " ++ show a ++ " as a CInt."

instance IsInitialValue CFloat where
  initialValue a = IVFloat a
  value (IVFloat a) = a
  value a = error $ "Attempt to extract the value of " ++ show a ++ " as a CFloat."

instance IsInitialValue String where
  initialValue a = IVString a
  value (IVString a) = a
  value a = error $ "Attempt to extract the value of " ++ show a ++ " as a String."

instance IsInitialValue () where
  initialValue a = IVVoid
  value IVVoid = ()
  value a = error $ "Attempt to extract the value of " ++ show a ++ " as ()."

typeof2 f = [typeDepiction ta, typeDepiction tb]
  where (ta,tb) = typeof2' f
        typeof2' :: (a->b) -> (a,b)
        typeof2' = undefined

typeof3 f = [typeDepiction ta, typeDepiction tb, typeDepiction tc]
  where (ta,tb,tc) = typeof3' f
        typeof3' :: (a->b->c) -> (a,b,c)
        typeof3' = undefined

sizeof TDInt   = sizeOf int
sizeof TDFloat = sizeOf float

alignmentof TDInt   = alignment int
alignmentof TDFloat = alignment float

typeShow TDInt   = "int"
typeShow TDFloat = "float"
typeShow TDVoid = "void"


----------------------------------------------------------------------
-- Node
----------------------------------------------------------------------

-- A reference is simply an Int. But to gain some type-safety
-- the reference are wrapped (below).
type Ref = Int

-- A typed reference.
newtype TRef a = TRef Ref
  deriving Show

type Rank = Int

-- e.g. Op ([Int,Int],Int) "plus" [a,b] [c] means the node Plus depends
-- on a and b (the parents) and c depends on it (c is a child of Plus).
-- Furthermore the type of the parents should match with the one of the Op.
-- A child has a rank higher than its parents, but not for a Delay node.
-- If a child of x is a delay, it is the delay of x.
-- The initial value of x, if x depends on its own delay, should be given.
--
-- The update mechanism is as follow :
-- if a node x should be updated (because one or more of its parents is/are
-- updated), all the children (and sub-children) and x itself are updated
-- according to their rank. In the children of x, it might be some delay
-- nodes which are constructed with a lower rank than x, so they will be
-- updated before x, using its value, before x itself is updated, possibly
-- using its preceding value stored in the delay.
--
-- TODO : There are two different Nodes : Signal and Event. When a signal
-- is updated, the update is propagated only if its value change. When
-- an event is updated (or just occurs if it has no value), the update
-- is always propagated.
--
-- The depict has always one element, except for Op.
-- The rank for Cst and In is always 0.
-- The parents for Cst and In is always [].
-- The children for Out is always [].
-- The depict for Out is always [].
-- A Delay has only one parent which has a *higher* rank.
data NodeKind = Cst | In | Out | Op | Delay
  deriving (Eq,Ord,Show)
data Node =
  Node {
    kind     :: NodeKind
  , initv    :: InitialValue
  , depict   :: [TypeDepiction]
  , info     :: String
  , parents  :: [Ref]
  , children :: [Ref]
  , ignored  :: [Ref] -- parent nodes whose updates are ignored.
  , rank     :: Rank
  }
  deriving Show

isCst = (== Cst) . kind
isIn  = (== In) . kind
isOut = (== Out) . kind
isOp  = (== Op) . kind
isDelay  = (== Delay) . kind

typ = last . depict

-- predicate to know if a node cnode has a parent's
-- reference pref but ignores it : the child is not
-- updated because of that parent.
cnode `ignores` pref = pref `elem` (ignored cnode)


----------------------------------------------------------------------
-- Graph
----------------------------------------------------------------------

data Heap = Heap { nodes :: IM.IntMap Node, nextName :: Ref }
  deriving Show

type N a = State Heap (TRef a)

emptyGraph = Heap IM.empty 0

graph gs = nodes (execState (go gs) emptyGraph)
  where go [] = return ()
        go (g:gs) = g >> go gs

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
dotOne1 g (r,node) = "n" ++ show r ++ " [" ++
  (concat $ intersperse ", " $ ["label=\"" ++ info node ++ "\""] ++ attr node)
  ++ "]\n"
  where attr n | isCst n = ["color=grey", "fontcolor=grey"]
               | isIn n = ["color=cyan"]
               | isOut n = ["color=orange"]
               | otherwise = []
dotRank1 g = concatMap (dotOne1 g)
dot1 g = concatMap (dotRank1 g) (grouped g)

-- arcs
dotOne2 g (r,node) = concatMap (\c -> "n" ++ show r ++ " -> n" ++ show c ++ " [" ++
  (concat $ intersperse ", " $ attr node c)
  ++"]\n") (children node)
  where attr n c | isCst n = ["color=grey"]
                 | isDelay (g IM.! c) = ["style=dashed"]
                 | otherwise = []
dotRank2 g = concatMap (dotOne2 g)
dot2 g = concatMap (dotRank2 g) (grouped g)

dotString g = 
  let g' = graph g in
  "digraph G {\n"
  ++ dot1 g'
  ++ "\n"
  ++ dot2 g'
  ++ "}\n"

writeAsDot fn g = writeFile fn (dotString g)

----------------------------------------------------------------------
-- C
----------------------------------------------------------------------

vars g = map var (byrank g)
var (r,node) | isOut node = ""
             | isIn node && typ node == TDVoid = " /* " ++ info node ++ " */"
             | isOp node && info node == "quit_on" = " /* " ++ info node ++ " */"
             | isCst node = (typeShow . typ) node ++ " " ++ cname (r,node) ++ " = " ++ info node ++ ";"
             | otherwise  = (typeShow . typ) node ++ " " ++ cname (r,node) ++ ";" ++ " /* " ++ info node ++ " */"
cname (r,n) | isCst n = "cst" ++ show r
            | isIn  n = "inp" ++ show r
            | isOp  n = "nod" ++ show r
            | isOut n = "out" ++ show r
            | isDelay n = "del" ++ show r

ups1 g = map up1 inputs
  where inputs = filter (isIn . snd) (byrank g)
up1 (r,node) | typ node == TDVoid = "void up" ++ show r ++ " ();\n"
  ++ "void up_" ++ info node ++ " ()\n{\n"
  ++ "up" ++ show r ++ " ();\n"
  ++ "}\n"
             | otherwise = "void up" ++ show r ++ " ();\n"
  ++ "void up_" ++ info node ++ " (" ++ (typeShow . typ) node ++ " x" ++ ")\n{\n"
  ++ cname (r,node) ++ " = x;\n"
  ++ "up" ++ show r ++ " ();\n"
  ++ "}\n"

ups2 g = map (up2 g) inputs
  where inputs = filter (isIn . snd) (byrank g)
up2 g (r,node) = "void up" ++ show r ++ " ()\n{\n" ++ body (r,node) g ++ "\n}"
body (r,node) g = concatMap (upNode g) depends
  where depends = sortByRank $ below g r
upNode g (r,node) | isOut node = "" -- no data to update for an output node
                  | isIn  node = error "input node shouldn't be updated from here"
                  | isCst node = "" -- no update for a constant node
                  | isOp  node = upOp g (r,node)
upOp g (r,node) =
  case (depict node,info node,parents node) of
    ([TDInt, TDInt, TDInt],"+",[a,b]) ->
      cname (r,node) ++ " = " ++ cname (a,g IM.! a) ++ " + " ++ cname (b,g IM.! b) ++ ";\n"
    ([TDInt, TDInt, TDInt],"-",[a,b]) ->
      cname (r,node) ++ " = " ++ cname (a,g IM.! a) ++ " - " ++ cname (b,g IM.! b) ++ ";\n"
    ([TDInt],"count",_) ->
      cname (r,node) ++ " ++;\n"
    ([TDVoid],"quit_on",_) ->
      "quit_loop = 1;\n"
    _ ->
      info node ++ " (" ++ cname (r,node) ++ ", " ++ intercalate ", " (map (cname' g) (parents node)) ++ ");\n"

outs g = concatMap outOne funs
  where outputs = filter (isOut . snd) (alist g)
        funs = map (info . snd) $ nubBy (\(_,node1) (_,node2) -> info node1 == info node2) outputs
        outOne name = "void out_" ++ name ++ " ()\n{\n" ++ body name ++ "\n}"
        body name = concatMap call $ filter ((== name) . info . snd) outputs
        call (r,node) = info node ++ " (" ++ intercalate ", " (map (cname' g) (parents node)) ++ ");\n"

cname' g r = cname (r,g IM.! r)

cCodeString ::  [State Heap a] -> String
cCodeString g = let g' = graph g in
  "#include <stdio.h>\n"
  ++" /* The loop can call the up_<input> and out_<output> functions. */\n"
  ++ " /* The <output> functions should be provided.                   */\n"
  ++ "int quit_loop;\n"
  ++ "void console (int i) { printf (\"%d\\n\", i); }\n"
  ++ (unlines $ vars g')
  ++ (unlines $ ups1 g')
  ++ (unlines $ ups2 g')
  ++ (outs g')
  ++ "\n"
  ++ "void loop ()\n"
  ++ "{\n"
  ++ "  up_milliseconds (100);\n"
  ++ "  up_milliseconds (200);\n"
  ++ "  out_console ();\n"
  ++ "  up_press_space ();\n"
  ++ "  up_press_space ();\n"
  ++ "  up_milliseconds (300);\n"
  ++ "  up_milliseconds (400);\n"
  ++ "  out_console ();\n"
  ++ "  up_milliseconds (500);\n"
  ++ "  up_milliseconds (600);\n"
  ++ "  out_console ();\n"
  ++ "  up_press_escape ();\n"
  ++ "}\n"
  ++ "int main ()\n"
  ++ "{\n"
  ++ "  quit_loop = 0;\n"
  ++ "  while (!quit_loop) { loop (); }\n"
  ++ "  return 0;\n"
  ++ "}\n"

ttcCode code = do
  putStrLn "Execution."
  s <- c_new
  c_set_output_type s tcc_OUTPUT_MEMORY
  withCString code (c_compile_string s)
  c_relocate s
  Just addr <- getSymbol s "loop"
  c_call addr
  c_delete s
  putStrLn "Done."

----------------------------------------------------------------------
-- Storable
----------------------------------------------------------------------

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
        sx = sizeof tx
        ax = alignmentof tx
        re = off `mod` ax -- how much is needed if any
        al = ax - re      -- padding to regain alignment if needed
        n  = node { children = map (offset mem) (children node) }
        n' = n { parents = map (offset mem) (parents n) }

-- translate from the map-ref (or alist-ref) to the memory-ref.
offset mem r = fst . fromJust $ lookup r mem

go (Memory size m) = do
  mem <- mallocForeignPtrBytes size
  return ()

----------------------------------------------------------------------
-- Graph
----------------------------------------------------------------------

instance Show (State Heap a) where
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

same g1 g2 (r1,r2) =
  let (n1,n2) = (g1 IM.! r1,g2 IM.! r2) in
  kind n1 == kind n2 &&
  initv n1 == initv n2 &&
  depict n1 == depict n2 &&
  info n1 == info n2 &&
  length (parents n1) == length (parents n2) &&
  (and $ map (same g1 g2) (zip (parents n1) (parents n2)))

instance (IsType n, Num n) => Num (N n) where
  (+) = lift2 (+) "+"
  (-) = lift2 (-) "-"
  (*) = lift2 (*) "*"
  negate = lift1 negate "negate"
  abs = lift1 abs "abs"
  signum = lift1 signum "signumf"
  fromInteger n = constant (fromInteger n) (show n)

instance (IsType n, Fractional n) => Fractional (N n) where
  (/) = lift2 (/) "/"
  recip = lift1 recip "recip"
  fromRational n = constant (fromRational n) (show $ fromRational n)

addChild' c n = if c `elem` children n then n else n { children = c : children n }

addParent' p n = if p `elem` parents n then n else n { parents = p : parents n }

-- Create a node (and give it automatically a name).
mkNode n = do
  i <- gets nextName
  ns <- gets nodes
  put $ Heap { nodes = IM.insert i n ns, nextName = i + 1 }
  return i

-- Add c as a child to the node n.
addChild c n = do
  change n (addChild' c)

addParent p n = do
  change n (addParent' p)

change n f = do
  modify (\g -> g { nodes = IM.adjust f n (nodes g) })

constant :: (IsType a) => a -> String -> N a
constant v info = mkNode (Node Cst (initialValue v) [(typeDepiction v)] info [] [] [] 0) >>= return . TRef

input :: (IsType a) => a -> String -> N a
input v info = mkNode (Node In (initialValue v) [(typeDepiction v)] info [] [] [] 0) >>= return . TRef

output info a = do
  TRef n1 <- a
  node <- gets ((IM.! n1) . nodes)
  n <- mkNode (Node Out IVNone [] info [n1] [] [] (rank node + 1))
  addChild n n1
  return (TRef n)

out info (TRef n1) = do
  node <- gets ((IM.! n1) . nodes)
  n <- mkNode (Node Out IVNone [] info [n1] [] [] (rank node + 1))
  addChild n n1
  return ()

lift1 :: (IsType a, IsType b) => (a -> b) -> String -> (N a -> N b)
lift1 f name = \a -> do
  r1 <- a
  op1 f name r1

lift2 :: (IsType a, IsType b, IsType c) => (a -> b -> c) -> String -> (N a -> N b -> N c)
lift2 f name = \a b -> do
  r1 <- a
  r2 <- b
  op2 f name r1 r2

op1 :: (IsType a, IsType b) => (a -> b) -> String -> TRef a -> N b
op1 f name (TRef n1) = do
  rk1 <- gets (rank . (IM.! n1) . nodes)
  iv1 <- gets (initv . (IM.! n1) . nodes)
  n <- mkNode (Node Op (initialValue $ f $ value iv1) (typeof2 f) name [n1] [] [] (rk1 + 1))
  addChild n n1
  return (TRef n)

op2 :: (IsType a, IsType b, IsType c) => (a -> b -> c) -> String -> TRef a -> TRef b -> N c
op2 f name (TRef n1) (TRef n2) = do
  rk1 <- gets (rank . (IM.! n1) . nodes)
  rk2 <- gets (rank . (IM.! n2) . nodes)
  iv1 <- gets (initv . (IM.! n1) . nodes)
  iv2 <- gets (initv . (IM.! n2) . nodes)
  n <- mkNode (Node Op (initialValue $ f (value iv1) (value iv2)) (typeof3 f) name [n1,n2] [] [] (max rk1 rk2 + 1))
  addChild n n1
  addChild n n2
  return (TRef n)

add :: TRef CInt -> TRef CInt -> N CInt
add = op2 (+) "+"

-- not useful at the moment : no way for the result to be triggered.
withDelay :: (IsType a) => a -> (N a -> N a) -> (N a)
withDelay v f = do
  d <- mkNode (Node Delay (initialValue v) [(typeDepiction v)] "delay" [] [] [] 0)
  (TRef x) <- share (return $ TRef d) f
  addChild x d
  addChild d x
  addParent x d
  rk1 <- gets (rank . (IM.! x) . nodes)
  change d (\d -> d { rank = pred rk1 })
  return (TRef x)

mkOp1 name init td n1 = do
  TRef r1 <- n1
  rk1 <- gets (rank . (IM.! r1) . nodes)
  n <- mkNode (Node Op (initialValue init) [TDInt] "name" [r1] [] [] (rk1 + 1))
  addChild n r1
  return (TRef n)

count :: (IsType a) => CInt -> N a -> N CInt
count init event = mkOp1 "count" init [TDInt] event

quit_on :: (IsType a) => N a -> N CInt
quit_on event = do
  TRef e <- event
  rk <- gets (rank . (IM.! e) . nodes)
  n <- mkNode (Node Op IVNone [TDVoid] "quit_on" [e] [] [] (rk + 1))
  addChild n e
  return (TRef n)


----------------------------------------------------------------------
-- Examples
----------------------------------------------------------------------

foo = lift2 f "foo"
f :: CInt -> CFloat -> String
f x s = "hello"

milliseconds = input (0::CInt) "milliseconds"
press_escape = input () "press_escape"
press_space = input () "press_space"

ex1 = [output "hey" $ (milliseconds + 45) `foo` (55.6 * 1.2)]

-- The main problem of this approch is showed
-- by dotString ex2 : the subgraph constructed by a
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
ex2 = [output "yah" $ a - a]
  where a = (milliseconds + 12 + 46)

-- no problem to discover sharing here but more ugly syntax.
ex3 = [do
  m <- milliseconds
  a <- add m m
  out "console" a
  ]

-- Better solution (thanks to Oleg Kiselyov) : like 'let', for sharing.
share :: N a -> (N a -> N b) -> N b
share x f = x >>= (f . return)

-- sharing occures !
ex4 = [share (milliseconds + 5) (\a -> output "console" $ a + a - 2)]

-- delay, but no way to update the value : it is never triggered.
ex5 = [output "console" $ withDelay 0 (\d -> d + (8::N CInt))]

ex_count = [
    output "console" $ count 0 press_space
  , output "console" $ (milliseconds + 5)
  , quit_on press_escape
  ]


