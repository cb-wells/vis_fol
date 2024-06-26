{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Lib ( readInitialMapFromFile, interactive ) where

import Prelude
import Data.List
import Data.Maybe
import Data.Either
import Data.List.Split (splitOn,splitPlaces)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.MultiSet (MultiSet, fromList, isSubsetOf)
import qualified Data.MultiSet as MultiSet

import System.IO
import System.Process
import System.Environment (getArgs)

import Text.Parsec
import Text.Parsec.String (Parser)
import Data.Char (isLetter, isDigit)
import Text.Parsec.Combinator (many1, between)
import Text.Parsec.Char (letter, char, digit, string, oneOf)

import Control.Applicative ((<$>), (<*>), (<*),  (<$))
import Control.Monad (void, guard)

import Debug.Trace

lstr :: [String] -> String
lstr ss = intercalate "," ss
istr :: [String] -> String
istr is = intercalate "_" is

width :: [a] -> Int
width xs = (length xs)

indx :: Eq a => a -> [a] -> Int
indx x xs = fromJust (elemIndex x xs)

cnt :: Eq a => a -> [a] -> Int
cnt vs c = length [x | x <- c, x==vs]

type KVMap = Map String String
type FileName = String

type Lbl = (Sym,Int)
type Loc = [Lbl]
type NodePf = String
type Dot = String

type XtraWt = Int
type Sh = Bool

type Name = String
type Sort = String
type Sym = String

type Ctx = [Sort]
type SI = (Sort,Int)

type LocCtx = [(Loc,SI)]
type LocSrts = [(Loc,Sort)]

data Trm =
  Var Sort Int
  | Tm Sym [SI] Sort
  | Ap Trm [Trm]
  deriving Eq

data Fol =
 Pred Name [Sort]
 | Sub Fol [Trm] Ctx
 | Img Fol [Trm]
 | And [Fol]
 | Not Fol
 | Tru
 -- xtras, pretty draw --
  | Or [Fol]
  | IfThen Fol Fol
  | All [SI] Fol

nstr :: Show a => [a] -> NodePf
nstr as = intercalate "_" [show a | a <- as]
astr :: [String] -> String
astr ls = intercalate " and " ls
ostr :: [String] -> String
ostr ls = intercalate " or " ls

g_pfx :: Dot -> Dot
g_pfx d = "graph g { \n" ++
          "splines=ortho; \n" ++
          "nodesep=1; \n" ++
          "ranksep=0.2;\n" ++
          "fontname=\"Courier New\"; \n" ++
          "fontsize = 18;\n" ++
          "esep=1;\n" ++
          "node [fontname=\"Courier New\", penwidth=2, fontsize=18,style=rounded]; \n" ++
          "edge [fontname=\"Courier New\", penwidth=2, fontsize=18];\n"
          ++ d ++ "}"

pol :: Fol -> Bool
pol (Not p) = not $ pol p
pol (Img p ts) = pol p
pol (Sub p ts c) = pol p
pol (And ps) = and (map pol ps)
pol (Pred p ss) = True
pol (Tru) = True
----------------
pol (Or ps) = and (map pol ps)
pol (IfThen p q) = True
pol (All sis p) = pol p

bg :: Bool -> Dot
bg b = if b then "white" else "lightgrey"

nbg :: Bool -> Dot
nbg p = bg (not p)

ctx :: Fol -> [Sort]
ctx (Pred p ss) = ss
ctx (And ps) = concat $ map ctx ps
ctx (Not p) = ctx p
ctx (Sub p ts c) = c
ctx (Img p ts) = tgts ts
ctx (Tru) = []
ctx (Or ps) = concat $ map ctx ps
ctx (IfThen p q) = ctx p ++ ctx q
ctx (All sis p) = (ctx p) \\ [s | (s,i) <- zip (ctx p) [0..],
                              notElem (s, absrel (ctx p) i) sis]

relabs :: SI -> Ctx -> Int
relabs (s,j) c =
  let sis = [(srt,i) | (srt,i) <- zip c [0..], srt == s]
      (srt,k) = sis!!j
   in k

absrel :: Ctx -> Int -> Int
absrel c k =
  let s = c!!k
      sis = [(srt,i) | (srt,i) <- zip c [0..], srt == s]
   in indx (s,k) sis

sym :: Trm -> Sym
sym (Var s i) = s ++ show i
sym (Tm f sis s) = f
sym (Ap u ts) = sym u

src :: Trm -> [SI]
src (Var s i) = [(s,i)]
src (Tm f sis s) = sis
src (Ap u ts) = concat $ map src ts

srcs :: [Trm] -> [SI]
srcs ts = concat $ map src ts

srcst :: [Trm] -> [Sort]
srcst ts = map fst (nub $ srcs ts)

tgt :: Trm -> Sort
tgt (Var s i) = s
tgt (Tm f sis s) = s
tgt (Ap u ts) = tgt u
tgts :: [Trm] -> [Sort]
tgts ts = [tgt t | t <- ts]

base_tms :: Trm -> Int -> Loc -> [(Trm,Loc)]
base_tms (Var s i) j n = [(Var s i, n++[("t",j)])]
base_tms (Tm f sis s) j n = [(Tm f sis s, n++[("t",j)])]
base_tms (Ap u ts) j n = concat [base_tms t k (n++[("t",j)]) | (t,k) <- zip ts [0..]]

validComp :: [Trm] -> [Trm] -> Bool
validComp ts0 ts1 =
  (tgts ts0) == [s | (s,i) <- srcs ts1]

comp :: [Trm] -> [Trm] -> [Trm]
comp ts0 ts1 =
  if not (validComp ts0 ts1)
  then error ("invalid composite:" ++ "\n ts0: " ++ show ts0 ++ "\n ts1: " ++ show ts1)
  else let is = [length (src t) | t <- ts1]
           ts0s = splitPlaces is ts0
        in [Ap t (ts0s!!i) | (t,i) <- zip ts1 [0..]]

instance {-# OVERLAPPING #-} Show Lbl where
  show (s,i) = s ++ show i
instance {-# OVERLAPPING #-} Show Loc where
  show as = nstr as
instance {-# OVERLAPPING #-} Show Ctx where
  show ss = lstr ss
instance {-# OVERLAPPING #-} Show Trm where
  show (Var s i) = s ++ show i
  show (Tm f sis s) = f ++ "(" ++ lstr [show si | si <- sis] ++ "):" ++ s
  show (Ap u ts) = (sym u) ++ "(" ++ lstr [show t | t <- ts] ++ "):" ++ tgt u

instance {-# OVERLAPPING #-} Show Fol where
  show (Pred p ss) = p -- ++ "[" ++ show ss ++ "]"
  show (Tru) = "1"
  show (Not p) = "not(" ++ show p ++ ")"
  show (And ps) = astr [show p | p <- ps]
  show (Or ps) = ostr [show p | p <- ps]
  show (IfThen p q) = "if(" ++ show p ++ ") then(" ++ show q ++ ")"
  show (All sis p) = "all " ++ show sis ++ ".(" ++ show p ++ ")"

  show (Sub (Pred p ss) ts c) =
    let wvs = [(s,i) | (s,i) <- zip c [0..], notElem (s, absrel c i) (srcs ts)]
     in p ++ "[" ++ lstr [show (ts!!ind) | (s,ind) <- zip ss [0..]] ++ "]"
        -- ++ "[" ++ lstr [show wv | wv <- wvs] ++ "]"
        ---- to show the weakened vs ----
  show (Sub (And ps) ts c) =
    let tss = sub_split ts ps
     in show (And $ [Sub p (tss!!i) c | (p,i) <- zip ps [0..]])  
  show (Sub (Not p) ts c)      = show (Not (Sub p ts c))
  show (Sub (Sub p ts1 c1) ts0 c0) = show (Sub p (comp ts0 ts1) c0)
  show (Sub (Img p ts0) ts1 c1) = "?"
  show (Sub (Tru) ts c) =
    let wvs = [(s,i) | (s,i) <- zip c [0..], notElem (s, absrel c i) (srcs ts)]
     in "wk" ++ "[" ++ lstr [show wv | wv <- wvs] ++ "]"
   
  show (Sub (Or ps) ts c) =
    let tss = sub_split ts ps
     in show (Or $ [Sub p (tss!!i) c | (p,i) <- zip ps [0..]]) 
  show (Sub (IfThen p q) ts c) = show (IfThen (Sub p ts c) (Sub q ts c))
  show (Sub (All sis p) ts c)    = show (All sis (Sub p ts c))
  
  show (Img p ts) =
    let trms = filter (not.fst.idVar) ts
        ands = if (null trms)
               then ""
               else " and " ++ lstr [show t | t <- trms] ++ "]"
     in "some[" ++ lstr ((ctx p)\\(srcst ts)) ++ "].(" ++ show p ++ ands ++ ")"


-- show or not (no-text option)
son :: Bool -> String -> String
son True s = s
son False s = ""
-------------------------------

sub_split :: [Trm] -> [Fol] -> [[Trm]]
sub_split ts ps = splitPlaces [length (ctx p) | p <- ps] ts

drawt :: Trm -> Loc -> Bool -> Dot
drawt (Tm f sis s) n ud =
  let shp = if ud then "triangle" else "invtriangle"
   in show n ++ "[style=filled, xlabel=\"\", label=\"" ++ f ++ "\","
      ++ "fillcolor=\"black\", fontcolor=\"white\", shape=" ++ shp ++ ", width=0.5];\n"

drawt (Var s i) n ud =
  show n ++ "[shape=point, label=\"\", xlabel=\"\"];\n"

drawt (Ap u ts) n ud =
  let shp = if ud then "triangle" else "invtriangle"
   in show n ++ "[style=filled, xlabel=\"\", label=\"" ++ (sym u) ++ "\","
      ++ " fillcolor=\"black\", fontcolor=\"white\", shape=" ++ shp ++ ", width=0.5];\n"
      ++ concat [if ud
                 then show (n ++ [("s",i)]) ++
                      "[shape=point,xlabel=\"" ++ tgt t ++ "\"];\n"
                      ++ (show n ++ " -- " ++ show (n ++ [("s",i)])) ++ "\n"
                      ++ drawt t (n++[("t",i)]) ud
                      ++ (show (n ++ [("s",i)]) ++ " -- " ++ show (n++[("t",i)])) ++ "\n"
                 else drawt t (n++[("t",i)]) ud
                      ++ (show (n++[("t",i)]) ++ " -- " ++ show n) ++ "\n"
                | (t,i) <- zip ts [0..]]

idVar :: Trm -> (Bool,SI)
idVar (Var s i) = (True,(s,i))
idVar (Tm f sis s) = (False,(s,0))
idVar (Ap u ts) = (False,(tgt u,0))


extend :: LocSrts -> Loc -> Sh -> Dot
extend nss node sh =
  "{rank=same;" ++
  concat [show (node++[("s",i)]) ++ "[shape=point, xlabel=\"" ++ son sh s ++ "\"];\n"
         | ((l,s),i) <- zip nss [0..]] ++ "}\n" ++
  concat [show l ++ " -- " ++ show (node++[("s",i)]) ++ ";\n"
         | ((l,s),i) <- zip nss [0..]]


extend_rel :: Ctx -> LocCtx -> Loc -> Sh -> Dot
extend_rel c nsis node sh =
  "{rank=same;\n" ++
  concat [show (node++[("s",k)]) ++ "[shape=point, xlabel=\"" ++ son sh s ++ "\"];\n"
         | (s,k) <- zip c [0..]] ++ "}\n" ++
  concat [let k = relabs (s,i) c
           in show n ++ " -- " ++ show (node++[("s",k)]) ++ ";\n"
         | (n,(s,i)) <- nsis]


extend_abs :: Ctx -> LocCtx -> Loc -> Sh -> Dot
extend_abs c nsis node sh =
  "{rank=same;\n" ++
  concat [show (node++[("s",i)]) ++ "[shape=point, xlabel=\"" ++ son sh s ++ "\"];\n"
         | (s,i) <- zip c [0..]] ++ "}\n" ++
  concat [show n ++ " -- " ++ show (node++[("s",i)]) ++ ";\n"
         | (n,(s,i)) <- nsis]

drawp :: Fol -> Loc -> Sh -> XtraWt -> Dot

drawp (Pred p ss) n sh w =
  let node = show n
   in node ++ "[shape=box, width=" ++ show w ++ ", label=\"" ++ p ++ "\"];\n" ++
      concat [let dot = show (n++[("s",i)])
                  str = son sh s
               in dot ++ "[shape=point, xlabel=\"" ++ str ++ "\"];\n" ++
                  node ++ " -- " ++ dot ++ ";\n"
             | (s,i) <- zip ss [0..]]

drawp Tru n sh w = ""

drawp (And ps) n sh w =
    let sign = and (map pol ps)
        b0 = if sign then "white" else "lightgrey"
        lbl = son sh (show (And ps))
          
        cs = [ctx p | p <- ps]
        locctx = concat [[(n++[("p",i),("s",j)],si)
                         | (si,j) <- zip (ctx p) [0..]]
                        | (p,i) <- zip ps [0..]]
     in "subgraph cluster_" ++ show n ++ "{\n bgcolor = \"" ++ b0 ++ "\";\n style=\"rounded\";\n"
        ++ concat [(drawp p (n++[("p",ind)]) sh w) ++ "\n" | (p,ind) <- zip ps [0..]]
        ++ "labelloc = \"b\"; label = \"" ++ lbl ++ "\" }\n\n"
        ++ extend locctx n sh
  
drawp (Not p) n sh w =
    let sign = pol p
        bg0 = if sign then "white" else "lightgrey"
        bg1 = if sign then "lightgrey" else "white"
        lbl = son sh ("not(" ++ (show p) ++ ")")
        
     in "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg1 ++ "\";"
        ++ "color=transparent;\n penwidth=0.5;\n"
        ++ "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg1
        ++ "\"; color=black; style=rounded; penwidth=2;\n"
        ++ "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg0 ++ "\";"
        ++ "style=dashed; penwidth=0.5; color=black;\n"
        ++ "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg0 ++ "\";"
        ++ "color=black; style=solid; penwidth=0.5; shape=box;\n"
        ++ drawp p (n++[("p",0)]) sh w ++ "}\n}\n"
        ++ "labelloc = \"b\"; label = \"" ++ lbl ++ "\"" ++ "}\n"
        ++ extend [(n++[("p",0),("s",i)],s) | (s,i) <- zip (ctx p) [0..]] n sh ++ "}\n"

drawp (Sub p ts c) n sh w
  | not (isSubsetOf (fromList (tgts ts)) (fromList (ctx p))) =
      error "invalid composite: \n" ++
      "ctx p: " ++ show (ctx p) ++ "\n" ++
      "tgts ts: " ++ show (tgts ts) ++ "\n"
  | otherwise =
      let pnd = n ++ [("u",0)]
          bts = concat [base_tms t i pnd | (t,i) <- zip ts [0..]]
          wvs = [(s,i) | (s,i) <- zip c [0..],
                 (notElem (s, absrel c i) tvs)]
          tvs = srcs ts
          cpys = [si | si <- tvs, cnt si tvs > 1]
          lcc = [(pnd++[("n", i)], (s,i)) | (s,i) <- zip c [0..]]
          sign = pol p
          lbl = son sh (show(Sub p ts c))
                      
       in "subgraph cluster_" ++ show n
          ++ "{\n bgcolor = \"" ++ bg sign ++ "\";\n style=\"rounded\";\n"
          ++ drawp p pnd sh (w) -- + length(ts) or ?
          ++ concat [let dot = pnd++[("n",i)]
                      in show dot ++ "[shape=point,label=\"\", xlabel=\"" ++ son sh s ++ "\"];\n"
                    | (s,i) <- zip c [0..]]
          ++ concat [drawt t (pnd++[("t",i)]) True
                     ++ show (pnd++[("s",i)]) ++ " -- " ++ show (pnd++[("t",i)]) ++ ";\n"
                    | (t,i) <- zip ts [0..]]
          ++ concat [let ind = relabs si c
                         nd = pnd++[("n",ind)]
                      in show nd ++ "[style=filled, label=\"\",fillcolor=\"black\""
                         ++ ",shape=triangle,width=0.2,regular=true];\n"
                    | si <- cpys]
          ++ concat [let nd = pnd++[("n",i)]
                      in show nd ++ "[style=filled, label=\"\",fillcolor=\"black\""
                         ++ ",shape=triangle,width=0.2,regular=true];\n"
                    | (s,i) <- wvs]
          ++ concat [concat [concat [show btn ++ " -- " ++
                                     show (pnd++[("n",relabs (s,j) c)]) ++ ";\n"
                                    | (s,j) <- src bt]
                            | (bt,btn) <- (base_tms t i pnd)]
                    | (t,i) <- zip ts [0..]]
          ++ "labelloc = \"b\"; label = \"" ++ lbl ++ "\"" ++ "\n}\n"
          ++ extend_abs c lcc n sh

drawp (Img p ts) n sh w
  | not (isSubsetOf (fromList (srcst ts)) (fromList (ctx p))) =
      error "invalid composite: \n" ++
      "ctx p: " ++ show (ctx p) ++ "\n" ++
      "srcs ts: " ++ show (srcst ts) ++ "\n"
  | otherwise = 
    let pnd = n ++ [("i",0)]
        c = ctx p
        sign = pol p
        b0 = if sign then "white" else "lightgrey"

        bts = concat [base_tms t i pnd | (t,i) <- zip ts [0..]]
        tvs = srcs ts
        cpys = [si | si <- tvs, cnt si tvs > 1] -------- here's where srcs /= ctx is good

        vis = [relabs (s,i) c | (s,i) <- tvs]
        dels = [i | (s,i) <- zip c [0..], notElem i vis]

        newc = [tgt t | t <- ts]
        lc = [(pnd++[("t",i)], (tgt t, absrel newc i))
             | (t,i) <- zip ts [0..]]

        lbl = son sh (show(Img p ts))

    in "subgraph cluster_" ++ show pnd
       ++ "{\n bgcolor = \"" ++ b0 ++ "\";\n style=\"rounded\";\n"
       ++ drawp p pnd sh (w) --  length(bts)-cpys ****
       ++ concat [let ind = relabs si c
                      nd = pnd++[("s",ind)]
                   in show nd ++ "[style=filled, label=\"\",fillcolor=\"black\""
                       ++ ",shape=invtriangle,width=0.2,regular=true];\n"
                 | si <- cpys]
       ++ concat [drawt t (pnd++[("t",i)]) False
                  ++ concat [concat [show (pnd++[("s",relabs (s,j) c)])
                                     ++ " -- " ++ show btn ++ ";\n"
                                    | (s,j) <- src bt]
                            | (bt,btn) <- (base_tms t i pnd)]
                 | (t,i) <- zip ts [0..]]
       ++ concat [show (pnd++[("s",i)]) ++ "[style=filled, label=\"\",fillcolor=\"black\""
                  ++ ",shape=invtriangle,width=0.2,regular=true];\n"
                 | i <- dels]
       ++ "labelloc = \"b\"; label = \"" ++ lbl ++ "\"" ++ "\n}\n"
       ++ extend_rel newc lc n sh


drawp (Or ps) n sh w = 
  let sign = pol (Or ps)
      b0 = bg sign
      b1 = nbg sign
      cs = [ctx p | p <- ps]
      locctx = concat [[(n++[("p",i),("s",j)], s)
                       | (s,j) <- zip (ctx p) [0..]]
                      | (p,i) <- zip ps [0..]]
      lbl = son sh (show (Or ps))
  in "subgraph cluster_" ++ show n ++ "{\n bgcolor = \"" ++ b0 ++ "\";\n style=\"rounded\";\n"
     ++ "subgraph cluster_" ++ show n ++ "_not{\n" ++ "bgcolor = \"" ++ b1 ++ "\";\n"
     ++ concat [let nd = n++[("p",ind)]
                 in "subgraph cluster_" ++ show nd ++ "{\n bgcolor = \"white\";\n" ++
                    (drawp p nd sh w) ++ "}\n"
               | (p,ind) <- zip ps [0..]]
     ++ "\n} labelloc = \"b\"; label = \"" ++ lbl ++ "\" }\n\n"
     ++ extend locctx n sh
  
drawp (IfThen p q) n sh w =
  let sign = pol (IfThen p q)
      b0 = bg sign
      b1 = nbg sign
      locctx = concat [[(n++[("p",i),("s",j)], s)
                       | (s,j) <- zip (ctx pred) [0..]]
                      | (pred,i) <- zip [p,q] [0..]]
      lbl = son sh ("if(" ++ show p ++ ") then(" ++ show q ++ ")")
    in  "subgraph cluster_" ++ show n ++ "{\n bgcolor = \"" ++ b0 ++ "\";\n"
        ++ "subgraph cluster_" ++ show n ++ "_not{\n" ++ "bgcolor = \"" ++ b1 ++ "\";\n"
        ++ (drawp p (n++[("p",0)]) sh w)
        ++ "subgraph cluster_" ++ show n ++ "0{\n bgcolor = \"white\";\n"
        ++ (drawp q (n++[("p",1)]) sh w) ++ "}\n"
        ++ "\n } labelloc = \"b\"; label = \"" ++ lbl ++ "\" }\n"
        ++ extend locctx n sh


drawp (All sis p) n sh w =
    let sign = pol (All sis p)
        b0 = bg sign
        b1 = nbg sign
        c = ctx p
        vis = [(s,relabs (s,i) c) | (s,i) <- sis]
        pnd = n ++ [("p",0)]
        lbl = son sh ("all " ++ show sis ++ ".(" ++ show(p) ++ ")")
  
    in  "subgraph cluster_" ++ show n ++ "{\n bgcolor = \"" ++ b0 ++ "\";\n"
        ++ "subgraph cluster_" ++ show n ++ "_not{\n" ++ "bgcolor = \"" ++ b1 ++ "\";\n"
        ++ "subgraph cluster_" ++ show n ++ "0{\n bgcolor = \"" ++ b0 ++ "\";\n"
        ++ drawp p pnd sh (w+length(sis)) ++ "}\n"        
        ++ concat [show (pnd++[("n",relabs (s,i) c)])
                   ++ "[style=filled, label=\"\",fillcolor=\"black\""
                   ++ ",shape=invtriangle,width=0.2,regular=true];\n"
                   ++ show (pnd++[("s",relabs (s,i) c)]) ++ " -- "
                   ++ show (pnd++[("n",relabs (s,i) c)]) ++ "\n"
                  | (s,i) <- sis]
        ++ concat [show (pnd++[("s",i),("e",0)]) ++
                   "[shape=point,label=\"" ++ s ++ "\"]\n" ++
                   show (pnd++[("s",i)]) ++ " -- " ++ show (pnd++[("s",i),("e",0)]) ++ "\n"
                  | (s,i) <- zip c [0..], notElem (s,i) vis]
        ++ "labelloc = \"b\"; label = \"" ++ lbl ++ "\" }\n"
        ++ extend [(pnd++[("s",i),("e",0)], s)
                  | (s,i) <- zip c [0..], notElem (s,i) vis] n sh ++ "}\n"

drawe :: Fol -> Fol -> Name -> Dot
drawe p q r =
    let bg = "white"
        n = [("p",0)]
        c0 = ctx p
        c1 = ctx q
        nc0 = [n++[("p",0),("s",i)] | (s,i) <- zip c0 [0..]]
     in "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg ++ "\";"
        ++ "color=transparent;\n penwidth=0.5;\n"
        ++ "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg
        ++ "\"; color=black; style=rounded; penwidth=2;\n"
        ++ "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg ++ "\";"
        ++ "style=dashed; penwidth=0.5; color=black;\n"
        ++ "subgraph cluster_" ++ show n ++ "{\n bgcolor=\"" ++ bg ++ "\";"
        ++ "color=black; style=solid; penwidth=0.5; shape=box;\n"
        ++ drawp p (n++[("p",0)]) True (length c0) ++ "}\n"
        ++ drawrel r (n++[("r",0)]) nc0 c0 c1 ++ "}\n"
        ++ "labelloc = \"b\"; label = \"" ++ show q ++ "\"" ++ "}\n"
        ++ extend [(n++[("r",0),("s",j)],s) | (s,j) <- zip c1 [0..]] n True ++ "}\n"

drawrel :: Name -> Loc -> [Loc] -> [Sort] -> [Sort] -> Dot
drawrel r node nc0 s0s s1s =
  show node ++ "[shape=box,label=\"" ++ r ++ "\"]\n" ++
  concat [show n ++ " -- " ++ show node ++ "\n" | n <- nc0] ++
  concat [show (node++[("s",i)]) ++ "[shape=point,label=\"" ++ s ++ "\"]\n" ++
          show node ++ " -- " ++ show (node++[("s",i)]) ++ "\n"
         | (s,i) <- zip s1s [0..]]

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace
identifier :: Parser String
identifier = lexeme ((:) <$> firstChar <*> many nonFirstChar)
  where firstChar = letter -- <|> char '_'
        nonFirstChar = digit <|> firstChar
whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"
commaSep p  = p `sepBy` (symbol ",")
symbol :: String -> Parser String
symbol s = try $ lexeme $ do
    u <- many1 (oneOf "<>=+-^%/*!|, ")
    guard (s == u)
    return s

pparen :: Parser a -> Parser a
pparen par = try $ do {spaces; string "("; spaces; z <- par; spaces; string ")"; return z}
pbracket :: Parser a -> Parser a
pbracket par = try $ do {spaces; string "["; spaces; z <- par; spaces; string "]";return z}
psym :: Parser a -> Parser (String,a)
psym par = try $ do {p<-identifier; z<-par; return (p,z)}
addspace :: Parser a -> Parser a
addspace par = do {spaces; z <- par; spaces; return z}
ssep :: String -> Parser a -> Parser [a]
ssep s par = sepBy par (string s)

parseInt :: Parser Int
parseInt = try $ do {i<-many1(digit); return $ read i}
parseSI :: Parser SI
parseSI = try $ do {s<-identifier; string "_"; i<-parseInt; return $ (s,i)}

parseVar :: Parser Trm
parseVar = try $ do {(s,i) <- parseSI; return $ Var s i}
parseTm :: Parser Trm
parseTm = try $ do {f <- identifier; string "(";
                    sis <- commaSep (parseSI); string ")";
                    string ":"; s <- identifier;
                    return $ Tm f sis s}
parseAp :: Parser Trm
parseAp = try $ do {(u,ts) <- psym(pparen(commaSep (parseTrm)));
                    spaces; string ":"; s <- identifier;
                    let sis = zip (tgts ts) [0..]
                     in return $ Ap (Tm u sis s) ts}
parseTrm :: Parser Trm
parseTrm = parseTm <|> parseVar <|> parseAp

parseVS :: Parser (String,String)
parseVS = try $ do {spaces; c <- identifier; char ':'; s <- identifier; return (c,s)}

parseFol :: Parser Fol
parseFol = 
  (try $ do {(p,ss) <- psym(pbracket (commaSep identifier));
                  return $ Pred p ss})
  <|> (try $ do {string "1"; return Tru})
  <|> (try $ do {spaces; char '('; spaces; ps <- (ssep "and" (addspace parseFol)); char ')';
                  return $ And ps})
  <|> (try $ do {spaces; string "not"; z <- pparen(parseFol);
                 return $ Not z})

  <|> (try $ do {spaces; string "~"; z <- pparen(parseFol);
                 return $ Not z})
  <|> (try $ do {spaces; char '('; spaces; ps <- (ssep "." (addspace parseFol)); char ')';
                  return $ And ps})

  <|> (try $ do {spaces; char '('; spaces; ps <- (ssep "or" (addspace parseFol)); char ')';
                  return $ Or ps})
  <|> (try $ do {string "if"; a <- pparen(parseFol); spaces;
                 string "then"; b <- pparen(parseFol);
                 return $ IfThen a b})
  <|> (try $ do {spaces; char '('; spaces; ps <- (ssep "+" (addspace parseFol)); char ')';
                  return $ Not(And [Not p | p <- ps])})
  <|> (try $ do {spaces; char '('; p <- addspace(parseFol);
                 string "/"; q <- addspace(parseFol); char ')';
                 return $ Not(And [p,Not(q)])}) 

  <|> (try $ do {char '('; p <- (addspace parseFol); char '<'; spaces;
                 char '['; spaces; ts <- commaSep(parseTrm); spaces; char '|'; spaces;
                 c <- commaSep(identifier); char ']'; spaces; char ')';
                 return $ Sub p ts c})
  <|> (try $ do {char '('; p <- (addspace parseFol); char '>'; spaces;
                 char '['; spaces; ts <- commaSep(parseTrm); spaces; char ']'; spaces; char ')';
                 return $ Img p ts})
  <|> (try $ do {spaces; string "some"; spaces;
                 sis <- commaSep(parseSI);
                 spaces; p <- pparen(parseFol);
                 return $ Img p [Var s (absrel (ctx p) i)
                                | (s,i) <- zip (ctx p) [0..],
                                  notElem (s,absrel (ctx p) i) sis] })

  
  <|> (try $ do {spaces; string "all"; spaces;
                 sis <- commaSep(parseSI);
                 spaces; p <- pparen(parseFol);
                 return $ All sis p })
  <|> (try $ do {char '('; p <- (addspace parseFol); string "->-"; spaces;
                 char '['; spaces; ts <- commaSep(parseTrm); spaces; char ']'; spaces; char ')';
                 return $ Not(Img (Not p) ts)})

  <|> (try $ do {string "att"; spaces; char '['; ys <- commaSep(parseVS); char ']';
                 spaces; char '['; spaces; ts <- commaSep(parseTrm); spaces; char ']';
                 let atts = [Tm av [] as | (av,as) <- ys]
                     srts = [as | (av,as) <- ys]
                  in return $ Sub (Img (Tru) atts) ts (srcst ts) })

  <|> (try $ do {string "match"; spaces; s <- identifier; spaces;
                 char '['; is <- commaSep(parseInt); char ']'; spaces;
                 p <- parseFol;
                 return $ match s is p} )

parseEnt :: Parser (Fol,Fol,Name)
parseEnt = try $ do {p <- addspace(parseFol); q <- addspace(parseFol);
                     r <- identifier; return $ (p,q,r)}

match :: Sort -> [Int] -> Fol -> Fol
match srt is p =
  let c = ctx p
      subc = [(s, absrel c i) | (s,i) <- zip c [0..],
              not ((s==srt)&&(elem (absrel c i) is))]
      n = (cnt srt c) - length(is)
      newc = map fst subc ++ [srt]
      ts = [if ((s==srt)&&(elem (absrel c i) is))
            then Var srt n
            else Var s (absrel c i)
           | (s,i) <- zip c [0..]]
   in Sub p ts newc

ent_draw :: String -> IO()
ent_draw pqr =
  do let par = parse parseEnt "" pqr
     case par of
       Left err -> print err
       Right (p,q,r) -> do writeFile "input.dot" (g_pfx (drawe p q r))
                           (_, _, _, _) <- createProcess (proc "dot"
                                           ["-Tsvg", "input.dot", "-o output.svg"])
                           putStrLn ""

fol_draw :: String -> Sh -> IO()
fol_draw s sh =
  do let par = (parse parseFol "" s)
     case par of
       Left err  -> print err
       Right  p  -> do writeFile "input.dot" (g_pfx (drawp p [("p",0)] sh (width(ctx p))))
                       (_, _, _, _) <- createProcess (proc "dot"
                                         ["-Tsvg", "input.dot", "-o output.svg"])
                       putStrLn ""

dot :: KVMap -> String -> Sh -> IO()
dot kv key sh = do
  case Map.lookup key kv of
        Just value -> do let par = (parse parseFol "" value)
                         case par of
                           Left err  -> print err
                           Right  p  -> do
                             putStrLn $ g_pfx (drawp p [("p",0)] sh (width $ ctx p))
        Nothing    -> putStrLn $ "Key '" ++ key ++ "' not found"

pprintMap :: KVMap -> String
pprintMap m = concat [ (fst kv) ++ " := " ++ (snd kv) ++ "\n"
                     | kv <- Map.toList m]

stoBool :: Char -> Bool
stoBool '0' = False
stoBool '1' = True
stoBool _   = error "invalid input; either 0 or 1."

interactive :: FileName -> KVMap -> IO ()
interactive fn kvmap = do
    putStrLn "\n[Key := Predicate]"
    putStrLn (pprintMap kvmap)
    putStrLn "[draw,load,set,delete,save]:"
    choice <- getLine
    case choice of
        ('l':'o':'a':'d':' ':sh:' ':key) -> do
          drawKey kvmap key (stoBool sh)
          interactive fn kvmap
        ('d':'r':'a':'w':' ':sh:' ':pred) -> do
          fol_draw pred (stoBool sh)
          interactive fn kvmap
        ('d':'o':'t':' ':sh:' ':key) -> do
          dot kvmap key (stoBool sh)
          interactive fn kvmap
        ('s':'e':'t':' ':sympred) -> do
            case keyOrToken kvmap sympred of
                Just pred -> do
                  let sym = head (words sympred)
                  putStrLn $ "new key-predicate: " ++ sym ++ " = " ++ pred ++ "\n"
                  interactive fn $ Map.insert (head (words sympred)) pred kvmap
                Nothing -> putStrLn "try again."
            interactive fn kvmap
        "save" -> do
          writeFile fn (pprintMap kvmap)
          interactive fn kvmap
        ('d':'e':'l':'e':'t':'e':' ':key) -> do
          interactive fn $ Map.delete key kvmap
        ('e':'n':'t':' ':pqss) -> do
          ent_draw pqss
          interactive fn kvmap
        _ -> do
            putStrLn "try again."
            interactive fn kvmap

drawKey :: KVMap -> String -> Sh -> IO ()
drawKey kvmap key sh = do
    case Map.lookup key kvmap of
        Just value -> fol_draw value sh
        Nothing    -> putStrLn $ "Key '" ++ key ++ "' not found"

keyOrToken :: KVMap -> String -> Maybe String
keyOrToken kvmap operation = case words operation of
    (newKey : ":=" : rest) -> do
        let result = intercalate " " $ map (\token -> if token `Map.member` kvmap
                                    then maybe "" id (Map.lookup token kvmap)
                                    else token) rest
        return result
    _ -> Nothing

readInitialMapFromFile :: FilePath -> IO KVMap
readInitialMapFromFile filePath = do
    contents <- readFile filePath
    let sl = map (splitOn " := ") (lines contents)
        pairs = [(p!!0,p!!1) | p <- sl]
    return $ Map.fromList pairs
