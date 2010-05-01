-- 2009.05.05
-- 2009.06.08
-- 2010.05.01
-- The Shunting-Yard algorithm (modified to allow function
-- application without parens around the arguments, and just
-- blanks between arguments).

module SY where

import Prelude hiding (init)

data Tree = Node [Tree]
-- The to-be-shunted tokens. Only the information for the
-- shunting yard algorithm is represented. Actual tokens should
-- be converted to this representation.
           | Num Int
           | Sym String
           | In [String] Associativity Precedence -- infix
           | L String -- left paren
           | R String -- right paren

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
  display' (In [s] _ _) = ' ' : s
  display' (In s _ _) = ' ' : concat s
  display' (R s) = ' ' : s
  display' (Node es) = ' ' : '(' : tail (concatMap display' es) ++ ")"

associativity (In _ a _) = a

prec (In _ _ p) = p

assoc = (Associative ==) . associativity
lAssoc = (LeftAssociative ==) . associativity
rAssoc = (RightAssociative ==) . associativity

isIn (In _ _ _) = True
isIn _ = False

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
          | Success
          | Blocked
          | Unexpected
  deriving (Show, Eq)

isDone sh = elem (rule sh)
  [Success, Blocked, UnmatchedL, UnmatchedR, Unexpected]

data Shunt = Shunt {
    input :: [Tree]    -- list of token (no Node)
  , stack :: [Tree]    -- stack of operators and applicators
  , output :: [[Tree]] -- stack of stacks
  , rule :: Rule
  }

instance Show Shunt where
  show (Shunt ts ss os r) =
    pad 20 ts ++ pad 20 ss ++ pad 20 os ++ "   " ++ show r

pad n s = let s' = show s in replicate (n - length s') ' ' ++ s'

steps s = do
  putStrLn $ "               Input               Stack              Output   Rule"
  let sh = iterate shunt $ init s
  let l = length $ takeWhile (not . isDone) sh
  mapM_ (putStrLn . show) (take (l + 1) sh)

init s = Shunt (map token $ tokenize s) [] [[]] Initial

parse ts = fix $ init ts
  where fix s = let s' = shunt s in
                if isDone s' then s' else fix s'

isLeft (Left a) = True
isLeft _ = False
isRight (Right a) = True
isRight _ = False

shunt :: Shunt -> Shunt

shunt (Shunt (t@(Num _):ts)    ss                  (os:oss)                _)
  =    Shunt ts                ss                  ((t:os):oss)            Inert

shunt (Shunt (t@(Sym _):ts)    (s@(Sym _):ss)      (os:oss) _)
  =    Shunt ts                (s:ss)              ((t:os):oss)            Application

shunt (Shunt (t@(Sym _):ts)    (s@(L "⟨"):ss)      (os:oss)                _)
  =    Shunt ts                (s:ss)              ((t:os):oss)            MatchedR

shunt (Shunt (t@(Sym _):ts)    ss                  (os:oss)                _)
  =    Shunt ts                (t:ss)              ([]:os:oss)             StackApp

shunt (Shunt (t@(In _ _ _):ts) (s@(L "⟨"):ss)      (os:oss)                _)
  =    Shunt ts                (s:ss)              ((t:os):oss)            MatchedR

shunt (Shunt (t@(In _ _ _):ts) (s@(In [_] _ _):ss) ((b:a:os):oss)          _)
  | t `lower` s =
       Shunt ts                (t:ss)              ((Node [s,a,b]:os):oss) StackOp
  | otherwise =
       Shunt ts                (t:s:ss)            ((b:a:os):oss)          StackOp

shunt (Shunt (t@(In _ _ _):ts) (s@(Sym _):ss)      (os:h:oss)              _)
  =    Shunt (t:ts)            ss                  ((ap:h):oss)            FlushApp
  where ap = if null os then s else Node (s : reverse os)

shunt (Shunt (t@(In _ _ _):ts) (s@(Node _):ss)     (os:h:oss)              _)
  =    Shunt (t:ts)            ss                  ((ap:h):oss)            FlushApp
  where ap = if null os then s else Node (s : reverse os)

shunt (Shunt (t@(In _ _ _):ts) ss                  (os:oss)                _)
  =    Shunt ts                (t:ss)              (os:oss)                StackOp

shunt (Shunt (t@(L "⟨"):ts)    ss                  (os:oss)                _)
  =    Shunt ts                (t:ss)              ([]:os:oss)             StackApp

shunt (Shunt (t@(L _):ts)      ss                  (os:oss)                _)
  =    Shunt ts                (t:ss)              (os:oss)                StackL

shunt (Shunt (t@(R "⟩"):ts)    (s@(L "⟨"):ss)      (os:h:oss)              _)
  =    Shunt ts                ss                  ((ap:h):oss)            MatchedR
  where ap = Node (reverse os)

shunt (Shunt (t:ts)            (s@(L "⟨"):ss)      (os:oss)                _)
  =    Shunt ts                (s:ss)              ((t:os):oss)            MatchedR

shunt (Shunt (t@(R _):ts)      (s@(L _):ss)        ((o:os):oss)            _)
  =    Shunt ts                (o':ss)             ([]:os:oss)             MatchedR
  where -- keep parenthesis around : (1 + ((a))) will be (+ 1 ((a))), not (+ 1 a).
        -- o' = case o of { Node [_] -> Node [o] ; Node _ -> o ; _ -> Node [o] }
        -- o' = case o of { Node [_] -> Node [o] ; Node _ -> Node [o] ; _ -> Node [o] }
        o' = o

shunt (Shunt []                (s@(L _):ss)        oss                     _)
  =    Shunt []                (s:ss)              oss                     UnmatchedL

shunt (Shunt (t@(R _):ts)      []                  (os:oss)                _)
  =    Shunt (t:ts)            []                  (os:oss)                UnmatchedR

shunt (Shunt (t@(R _):ts)      (s@(In [_] _ _):ss) ((b:a:os):oss)          _)
  =    Shunt (t:ts)            ss                  ((Node [s,a,b]:os):oss) FlushOp

shunt (Shunt (t@(R _):ts)      (s@(Sym _):ss)      (os:h:oss)              _)
  =    Shunt (t:ts)            ss                  ((ap:h):oss)            FlushApp
  where ap = if null os then s else Node (s : reverse os)

shunt (Shunt (t@(R _):ts)      (s@(Node _):ss)     (os:h:oss)              _)
  =    Shunt (t:ts)            ss                  ((ap:h):oss)            FlushApp
  where ap = if null os then s else Node (s : reverse os)

shunt (Shunt []                (s@(In [_] _ _):ss) ((b:a:os):oss)          _)
  =    Shunt []                ss                  ((Node [s,a,b]:os):oss) FlushOp

shunt (Shunt []                (s@(Sym _):ss)      (os:h:oss) _)
  =    Shunt []                ss                  ((ap:h):oss)            FlushApp
  where ap = if null os then s else Node (s : reverse os)

shunt (Shunt []                (s@(Node _):ss)     (os:h: oss)             _)
  =    Shunt []                ss                  ((ap:h):oss)            FlushApp
  where ap = if null os then s else Node (s : reverse os)

shunt (Shunt []                []                  [[o]]                   _)
  =    Shunt []                []                  [[o]]                   Success

shunt sh = sh { rule = Unexpected }

lower o1 o2 | assoc o1 || (lAssoc o1 && prec o1 <= prec o2) = True
            | rAssoc o1 && prec o1 < prec o2 = True
            | otherwise = False

tokenize = words . tokenize'
tokenize' ('(':cs) = " ( " ++ tokenize' cs
tokenize' (')':cs) = " ) " ++ tokenize' cs
tokenize' ('⟨':cs) = " ⟨ " ++ tokenize' cs
tokenize' ('⟩':cs) = " ⟩ " ++ tokenize' cs
tokenize' (c:cs) = c : tokenize' cs
tokenize' [] = []

token (c:_) | c `elem` ['a'..'z'] = Sym [c]
            | c == '+' = In ["+"] LeftAssociative 6
            | c == '-' = In ["-"] LeftAssociative 6
            | c == '*' = In ["*"] LeftAssociative 7
            | c == '/' = In ["/"] LeftAssociative 7
            | c == '(' = L "("
            | c == '⟨' = L "⟨"
            | c == ')' = R ")"
            | c == '⟩' = R "⟩"
            | otherwise = Num (read [c])

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
  ("1 + (f a) 2","(+ 1 ((f a) 2))"),

  ("2","2")
  ]

checkTests = mapM_ check tests
  where check (i,o) = do case parse i of
                           Shunt [] [] [[o']] Success ->
                            if o == show o' then return ()
                                       else do putStrLn $ "FAIL: input: " ++ i
                                                 ++ ", expected: " ++ o
                                                 ++ ", computed: " ++ show o'
                                               steps i
                           _ -> do putStrLn $ "FAIL: input: " ++ i
                                     ++ ", expected: " ++ o
                                     ++ ", computed: Nothing."
                                   steps i
                           

