--------------------------------------------------------------------------------
-- Pretty Printer

module Language.OutSystems.Pretty where

import Relude

import qualified Language.OutSystems.Lang as L

import qualified Text.PrettyPrint.HughesPJ as P
import Text.PrettyPrint.HughesPJ ((<+>))


newtype Pretty a = Pretty { pretty :: P.Doc }

fun :: String -> [P.Doc] -> Pretty a
fun name args = Pretty $
  P.text name <> P.parens (fold $ P.punctuate (P.comma <> P.space) args)

binop :: String -> P.Doc -> P.Doc -> Pretty a
binop op x y  = Pretty $ P.parens (x <+> P.text op <+> y)

unop :: String -> P.Doc -> Pretty a
unop op x = Pretty $ P.parens (P.text op <> x)

eq :: P.Doc -> P.Doc -> Pretty a
eq = binop "+"

leq :: P.Doc -> P.Doc -> Pretty a
leq = binop "<="

instance L.LangText Pretty where
  int x = Pretty $ P.int x
  text t = Pretty $ P.text (show t) -- P.doubleQuotes $ P.text $ T.unpack t

  length (Pretty t) = fun "Length" [t]
  substr (Pretty t) (Pretty x) (Pretty y) = fun "Substr" [t, x, y]
  concat (Pretty t0) (Pretty t1) = fun "Concat" [t0, t1]

  chr (Pretty x) = fun "Chr" [x]

  index0 (Pretty t0) (Pretty t1) = fun "Index" [t0, t1]
  index1 (Pretty t0) (Pretty t1) (Pretty x) = fun "Index" [t0, t1, x]

  replace (Pretty t0) (Pretty t1) (Pretty t2) = fun "Replace" [t0, t1, t2]

  lower (Pretty t) = fun "Lower" [t]
  upper (Pretty t) = fun "Upper" [t]

  trimEnd (Pretty t) = fun "TrimEnd" [t]
  trimStart (Pretty t) = fun "TrimStart" [t]
  trim (Pretty t) = fun "Trim" [t]

instance L.LangBool Pretty where
  bool x = Pretty $ P.text (show x)

  if_ (Pretty b) (Pretty x) (Pretty y) = fun "If" [b, x, y]
  or  (Pretty x) (Pretty y) = binop "or" x y
  not (Pretty b) = unop "not" b

  eqBool (Pretty x) (Pretty y) = eq x y
  eqText (Pretty x) (Pretty y) = eq x y
  eqInt  (Pretty x) (Pretty y) = eq x y

  leqText (Pretty x) (Pretty y) = leq x y
  leqInt  (Pretty x) (Pretty y) = leq x y

instance L.LangArith Pretty where
  uminus (Pretty x) = unop "-" x

  minus (Pretty x) (Pretty y) = binop "-" x y
  plus  (Pretty x) (Pretty y) = binop "+" x y
  mult  (Pretty x) (Pretty y) = binop "*" x y
  div   (Pretty x) (Pretty y) = binop "/" x y
