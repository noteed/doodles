-- 2009.05.05
-- 2009.06.08
-- 2010.05.01
-- The Shunting-Yard algorithm (modified to allow function
-- application without parens around the arguments, and just
-- blanks between arguments).
-- TODO make sure the rules reflect what's going on, a same
-- rule should be associated to a same behavior.
-- TODO the precedence comparison should depends on the
-- associativity even for Pre/Postfix (see 'lower').
-- TODO factorize
-- TODO regroup Closed and L and R

module SY where

import Data.List

data Tree = Node [Tree]
-- The to-be-shunted tokens. Only the information for the
-- shunting yard algorithm is represented. Actual tokens should
-- be converted to this representation.
           | Num Int
           | Sym String
           | Op [String] -- on the stack, TODO turn into Sym on the output
           | L String -- left paren
           | R String -- right paren

data Op = Infix [String] [String] Associativity Precedence -- infix
        | Prefix [String] [String] Precedence -- prefix
        | Postfix [String] [String] Precedence -- postfix
        | Closed [String] [String]

data Associativity = Associative | LeftAssociative | RightAssociative
  deriving (Show, Eq)

type Precedence = Int

instance Show Tree where
  show = display

display :: Tree -> String
display = tail . display'
  where
  display' (Num i) = ' ' : show i
  display' (Sym s) = ' ' : s
  display' (L s) = ' ' : s
  display' (Op l) = ' ' : concat l
  display' (R s) = ' ' : s
  display' (Node es) = ' ' : '(' : tail (concatMap display' es) ++ ")"

associativity (Infix _ _ a _) = a

prec (Infix _ _ _ p) = p

assoc = (Associative ==) . associativity
lAssoc = (LeftAssociative ==) . associativity
rAssoc = (RightAssociative ==) . associativity

isInfix (Infix _ _ _ _) = True
isInfix _ = False

isInfix' (Infix xs _ _ _) ys = xs == ys
isInfix' _ _ = False

data Rule = Initial
          | Inert -- not an operator or an applicator
          | Application
          | FlushApp
          | StackApp
          | FlushOp
          | StackOp
          | StackL
          | UnmatchedL
          | UnmatchedR
          | MatchedR
          | SExpr
          | Success
          | Blocked
          | Unexpected
  deriving (Show, Eq)

isDone sh = elem (rule sh)
  [Success, Blocked, UnmatchedL, UnmatchedR, Unexpected]

data Shunt = S {
    input :: [Tree]    -- list of token (no Node)
  , stack :: [Tree]    -- stack of operators and applicators
  , output :: [[Tree]] -- stack of stacks
  , rule :: Rule
  }

instance Show Shunt where
  show (S ts ss os r) =
    pad 20 ts ++ pad 20 ss ++ pad 20 os ++ "   " ++ show r

pad n s = let s' = show s in replicate (n - length s') ' ' ++ s'

steps s = do
  putStrLn $ "               Input               Stack              Output   Rule"
  let sh = iterate shunt $ initial s
  let l = length $ takeWhile (not . isDone) sh
  mapM_ (putStrLn . show) (take (l + 1) sh)

initial s = S (map token $ tokenize s) [] [[]] Initial

parse ts = fix $ initial ts
  where fix s = let s' = shunt s in
                if isDone s' then s' else fix s'

isLeft (Left a) = True
isLeft _ = False
isRight (Right a) = True
isRight _ = False

shunt :: Shunt -> Shunt
shunt sh = case sh of

  S   ts                (s@(Op y):ss)      ([a]:oss) _ ->
    case findOps y someTable of
      [Postfix _ [] _] -> S (Node [s,a]:ts)    ss           ([]:oss)       FlushApp
      [Closed _ []] -> S (Node [s,a]:ts)    ss           ([]:oss)       FlushApp
      _ -> shunt' sh
  _ -> shunt' sh

shunt' sh = case sh of

  S   (t@(Num _):ts)    ss                  (os:oss)                _ ->
    S ts                ss                  ((t:os):oss)            Inert

  S   (t@(Sym _):ts)    (s@(L "⟨"):ss)      (os:oss)                _ ->
    S ts                (s:ss)              ((t:os):oss)            SExpr

  S   (t@(Node _):ts)   (s@(L "⟨"):ss)      (os:oss)                _ ->
    S ts                (s:ss)              ((t:os):oss)            SExpr

  S   (t@(Sym x):ts)    (s@(Sym _):ss)      (os:oss) _ ->
    case findOp x someTable of
      [] -> S ts        (s:ss)              ((t:os):oss)          Application
      [Prefix [_] _ _] -> S ts    (t:s:ss)     ([]:os:oss)           StackOp
      [Closed [_] _] -> S ts   (t:s:ss)     ([]:os:oss)           StackOp
      _ ->  S (t:ts)    ss                  (apply s $ os:oss)    FlushApp

  S   (t@(Node _):ts)   (s@(Sym _):ss)      (os:oss)                _ ->
    S ts                (s:ss)              ((t:os):oss)            Application

  S   (t@(Sym x):ts) (s@(Op y):ss) oss      _ ->
    case (findOp x someTable, findOps y someTable) of
      ([], _) -> S ts   (t:s:ss)            ([]:oss)             StackApp
      ([o1@(Infix [_] [] _ _)], [o2@(Infix [_] [] _ _)])
        | o1 `lower` o2 ->
          -- TODO possibly flush more ops
          S ts      (Op [x]:ss)           (apply s oss) StackOp
        | otherwise ->
          S ts      (Op [x]:s:ss)         oss          StackOp
      ([o1@(Infix l1 r1 _ _)], [o2@(Infix l2 (r2:r2s) _ _)])
        | l2++[r2] == l1 ->
          S ts      (Op l1:ss)            oss          StackOp
      ([o1@(Infix [_] _ _ _)], [o2@(Infix _ [] _ _)])
        | o1 `lower` o2 ->
          -- TODO possibly flush more ops
          S ts      (Op [x]:ss)           (apply s oss) StackOp
        | otherwise ->
          S ts      (Op [x]:s:ss)         oss          StackOp
      ([o1@(Infix _ _ _ p1)], [o2@(Prefix _ _ p2)])
        | p1 > p2 ->
          S ts      (Op [x]:s:ss)         oss          StackOp
        | p1 < p2 ->
          S ts      (Op [x]:ss)           (apply s oss) StackOp
      ([o1@(Prefix [_] _ _)], [o2@(Infix [_] _ _ _)]) ->
          S ts      (Op [x]:s:ss)         oss          StackOp
      ([o1@(Prefix [_] [] _)], [o2@(Prefix [_] [] _)]) ->
          S ts      (Op [x]:s:ss)         oss          StackOp
      ([o1@(Prefix l1 r1 _)], [o2@(Prefix l2 (r2:r2s) _)])
        | l2++[r2] == l1 ->
          S ts      (Op l1:ss)            oss          StackOp
      ([o1@(Postfix [_] [] p1)], [o2@(Prefix [_] [] p2)])
        | p1 > p2 ->
          S ts      (Op [x]:s:ss)         oss          StackOp
        | p1 < p2 ->
          S ts      (Op [x]:ss)           (apply s oss) StackOp
        | otherwise -> error $ "precedence cannot be mixed: " ++ show t ++ ", " ++ show s
      ([o1@(Closed l1 [])], [o2@(Closed l2 [r2])])
        | l2++[r2] == l1 ->
          S (o:ts)           ss       (os:oss')      MatchedR
          where ((o:os):oss') = apply (Op l1) oss
      ([o1], [o2@(Closed _ _)]) ->
          S ts      (Op [x]:s:ss)         oss          StackOp
      ([o1@(Closed _ _)], [_]) ->
          S (t:ts)            ss                  (apply s oss) FlushOp
      _ -> error $ "TODO: " ++ show t ++ ", " ++ show s

  S   (t@(Node _):ts) (s@(Op _):ss)       oss                  _ ->
    S ts              (t:s:ss)            ([]:oss)             StackApp

  S   (t@(Sym x):ts) (s@(Node _):ss)   (os:oss)              _ ->
    case findOp x someTable of
      [] -> S ts        (s:ss)              ((t:os):oss)          Application
      _ -> S (t:ts)     ss                  (apply s $ os:oss)            FlushApp

  S   (t@(Node _):ts) (s@(Node _):ss)       (os:oss)              _ ->
    S ts              (s:ss)                ((t:os):oss)          Application

  S   (t@(Sym x):ts)    ss                  (os:oss)                _ ->
    case findOp x someTable of
      [] -> S ts       (t:ss)              ([]:os:oss)             StackApp
      -- x is the first sub-op, and the stack is empty or has a left bracket at its top.
      _ -> case findOps [x] someTable of
        [] -> error "using middle sub-op as first sub-op"
        _ -> S ts      (Op [x]:ss)  (os:oss)  StackOp

  S   (t@(Node _):ts)    ss                  (os:oss)                _ ->
    S ts                 (t:ss)              ([]:os:oss)             StackApp

  S   (t@(L "⟨"):ts)    ss                  (os:oss)                _ ->
    S ts                (t:ss)              ([]:os:oss)             StackApp

  S   (t@(L _):ts)      ss                  (os:oss)                _ ->
    S ts                (t:ss)              (os:oss)                StackL

  S   (t@(R "⟩"):ts)    (s@(L "⟨"):ss)      (os:h:oss)              _ ->
    S ts                ss                  ((ap:h):oss)            MatchedR
    where ap = Node (reverse os)

  S   (t:ts)            (s@(L "⟨"):ss)      (os:oss)                _ ->
    S ts                (s:ss)              ((t:os):oss)            SExpr

  S   []                (s@(L _):ss)        oss                     _ ->
    S []                (s:ss)              oss                     UnmatchedL

  S   (t@(R _):ts)      (s@(L _):ss)        ((o:os):oss)            _ ->
    S (o':ts)           ss             (os:oss)             MatchedR
    where -- keep parenthesis around : (1 + ((a))) will be (+ 1 ((a))), not (+ 1 a).
          -- o' = case o of { Node [_] -> Node [o] ; Node _ -> o ; _ -> Node [o] }
          -- o' = case o of { Node [_] -> Node [o] ; Node _ -> Node [o] ; _ -> Node [o] }
          o' = o

  S   (t@(R _):ts)      []                  (os:oss)                _ ->
    S (t:ts)            []                  (os:oss)                UnmatchedR

  S   (t@(R _):ts)      (s@(Op _):ss)       oss          _ ->
    S (t:ts)            ss                  (apply s oss) FlushOp

  S   (t@(R _):ts)      (s@(Sym _):ss)      oss              _ ->
    S (t:ts)            ss                  (apply s oss)            FlushApp

  S   (t@(R _):ts)      (s@(Node _):ss)     oss              _ ->
    S (t:ts)            ss                  (apply s oss)            FlushApp

  S   []                (s@(Op _):ss) oss          _ ->
    S []                ss                  (apply s oss) FlushOp

  S   []                (s@(Sym _):ss)      oss _ ->
    S []                ss                  (apply s oss)            FlushApp

  S   []                (s@(Node _):ss)     oss             _ ->
    S []                ss                  (apply s oss)            FlushApp

  S   []                []                  [[o]]                   _ ->
    S []                []                  [[o]]                   Success

  _ -> sh { rule = Unexpected }

lower o1@(Infix [_] _ _ _) o2@(Infix _ [] _ _)
    | assoc o1 || (lAssoc o1 && prec o1 <= prec o2) = True
    | rAssoc o1 && prec o1 < prec o2 = True
lower _ _ = False

tokenize = words . tokenize'
tokenize' ('(':cs) = " ( " ++ tokenize' cs
tokenize' (')':cs) = " ) " ++ tokenize' cs
tokenize' ('⟨':cs) = " ⟨ " ++ tokenize' cs
tokenize' ('⟩':cs) = " ⟩ " ++ tokenize' cs
tokenize' (c:cs) = c : tokenize' cs
tokenize' [] = []

token (c:cs) | c `elem` ['a'..'z'] ++ "+-*/?:#i°%!<>" = Sym (c:cs)
             | c == '(' = L "("
             | c == '⟨' = L "⟨"
             | c == ')' = R ")"
             | c == '⟩' = R "⟩"
             | otherwise = Num (read [c])

someTable =
 [ Infix [] ["+"] LeftAssociative 6
 , Infix [] ["-"] LeftAssociative 6
 , Infix [] ["*"] LeftAssociative 7
 , Infix [] ["/"] LeftAssociative 7
 , Infix [] ["?",":"] RightAssociative 5
 , Infix [] ["?'", ":'"] RightAssociative 9
 , Prefix [] ["#"] 8
 , Postfix [] ["°"] 7
 , Postfix [] ["%"] 8
 , Postfix [] ["!"] 9
 , Prefix [] ["if","then","else"] 1
 , Closed [] ["</","/>"]
 ]

findOp op [] = []
findOp op (Infix [] parts a p:xs)
  | op `elem` parts =
     let (l,r) = break' (== op) parts
     in Infix l r a p : findOp op xs
  | otherwise = findOp op xs
findOp op (Prefix [] parts p:xs)
  | op `elem` parts =
     let (l,r) = break' (== op) parts
     in Prefix l r p : findOp op xs
  | otherwise = findOp op xs
findOp op (Postfix [] parts p:xs)
  | op `elem` parts =
     let (l,r) = break' (== op) parts
     in Postfix l r p : findOp op xs
  | otherwise = findOp op xs
findOp op (Closed [] parts:xs)
  | op `elem` parts =
     let (l,r) = break' (== op) parts
     in Closed l r : findOp op xs
  | otherwise = findOp op xs

findOps ops [] = []
findOps ops (Infix [] parts a p:xs)
  | ops `isPrefixOf` parts = Infix ops (drop (length ops) parts) a p : findOps ops xs
  | otherwise = findOps ops xs
findOps ops (Prefix [] parts p:xs)
  | ops `isPrefixOf` parts = Prefix ops (drop (length ops) parts) p : findOps ops xs
  | otherwise = findOps ops xs
findOps ops (Postfix [] parts p:xs)
  | ops `isPrefixOf` parts = Postfix ops (drop (length ops) parts) p : findOps ops xs
  | otherwise = findOps ops xs
findOps ops (Closed [] parts:xs)
  | ops `isPrefixOf` parts = Closed ops (drop (length ops) parts) : findOps ops xs
  | otherwise = findOps ops xs

break' p ls = case break p ls of
  (_, []) -> error "break': no element in l satisfying p"
  (l, r) -> (l ++ [head r], tail r)

apply s@(Op y) (os:oss) = (Node (s:reverse l) : r) : oss
  where nargs = case findOps y someTable of
          [Infix _ _ _ _] -> length y + 1
          [_] -> length y
        (l,r) = splitAt nargs os -- TODO test correct lenght of os
apply s@(Sym _) (os:h:oss) =  (ap:h):oss
  where ap = if null os then s else Node (s:reverse os)
apply s@(Node _) (os:h:oss) =  (ap:h):oss
  where ap = if null os then s else Node (s:reverse os)
apply s oss = error $ "can't apply " ++ show s ++ " to " ++ show oss

-- [(input, expected output)]
tests :: [(String,String)]
tests = [
  ("1","1"),
  ("a","a"),

  ("1 + 2","(+ 1 2)"),
  ("a + 2","(+ a 2)"),
  ("1 + b","(+ 1 b)"),
  ("a + b","(+ a b)"),
  ("1 * 2","(* 1 2)"),

  ("1 + 2 + 3","(+ (+ 1 2) 3)"),
  ("1 + 2 * 3","(+ 1 (* 2 3))"),
  ("1 * 2 + 3","(+ (* 1 2) 3)"),
  -- TODO test case with 3 binary infix operator with different priorities

  ("f a","(f a)"),
  ("f 1","(f 1)"),
  ("f a b","(f a b)"),
  ("f 1 b","(f 1 b)"),
  ("f a 1","(f a 1)"),

  ("f a + 1","(+ (f a) 1)"),
  ("1 + f a","(+ 1 (f a))"),

  ("(a)","a"),
  ("((a))","a"),
  ("1 + (a)","(+ 1 a)"),
  ("1 + ((a))","(+ 1 a)"),
  ("(1 + 2)","(+ 1 2)"),
  ("(1 + (a))","(+ 1 a)"),
  ("(1 + ((a)))","(+ 1 a)"),

  ("1 * (2 + 3)","(* 1 (+ 2 3))"),
  ("(1 + 2) * 3","(* (+ 1 2) 3)"),
  ("1 + (f a)","(+ 1 (f a))"),
  ("(f a) + 1","(+ (f a) 1)"),
  ("(f a b) 1","((f a b) 1)"),
  ("(f a b) 1 2","((f a b) 1 2)"),
  ("1 + (f a) 2","(+ 1 ((f a) 2))")
  , ("f (a + b) (1 - 2)", "(f (+ a b) (- 1 2))")

  , ("⟨1⟩", "(1)")
  , ("⟨a⟩", "(a)")
  , ("⟨⟨1⟩⟩", "((1))")
  , ("⟨⟨a⟩⟩", "((a))")
  , ("⟨+ a b⟩", "(+ a b)")
  , ("⟨+ a b⟩ * (1 - 2)", "(* (+ a b) (- 1 2))")
  , ("(a + b) * ⟨- 1 2⟩", "(* (+ a b) (- 1 2))")
  , ("⟨* (a + b) (1 - 2)⟩", "(* (+ a b) (- 1 2))")
  , ("⟨* (a + b) ⟨- 1 2⟩⟩", "(* (+ a b) (- 1 2))")

  , ("true ? 1 : 0", "(?: true 1 0)") -- TODO this sould be _?_:_ or __?__:__ or ␣?␣:␣
  , ("true ? 1 : 0 + 1", "(?: true 1 (+ 0 1))")
  , ("true ?' 1 :' 0 + 1", "(+ (?':' true 1 0) 1)")

  , ("# a", "(# a)")
  , ("a # b", "(a (# b))")
  , ("# # a", "(# (# a))")

  , ("a !", "(! a)")
  , ("a ! b", "((! a) b)")
  , ("a ! !", "(! (! a))")

  , ("# a °", "(° (# a))")
--  , ("# a %", Error "precedence cannot be mixed")
  , ("# a !", "(# (! a))")

  , ("if true then 1 else 0", "(ifthenelse true 1 0)")
  , ("if 2 then 1 else 0", "(ifthenelse 2 1 0)")
  , ("if a b then 1 else 0", "(ifthenelse (a b) 1 0)")
  , ("if true then a b else 0", "(ifthenelse true (a b) 0)")
  , ("if true then 1 else a b", "(ifthenelse true 1 (a b))")
  , ("1 + if true then 1 else 0", "(+ 1 (ifthenelse true 1 0))")
  , ("1 + if true then 1 else a b + c", "(+ 1 (ifthenelse true 1 (+ (a b) c)))")

  , ("</ a />","(<//> a)")
  , ("</ 0 />","(<//> 0)")
  , ("</ f a b />","(<//> (f a b))")
  , ("</ f 1 2 />","(<//> (f 1 2))")
  , ("</ a + b />","(<//> (+ a b))")

  , ("2","2")
  ]

checkTests = mapM_ check tests

check (i,o) = case parse i of
  S [] [] [[o']] Success ->
    if o == show o'
    then return ()
    else do putStrLn $ "FAIL: input: " ++ i
              ++ ", expected: " ++ o
              ++ ", computed: " ++ show o'
            steps i
  _ -> do putStrLn $ "FAIL: input: " ++ i
            ++ ", expected: " ++ o
            ++ ", computed: Nothing."
          steps i
                           

