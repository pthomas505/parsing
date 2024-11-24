-- https://serokell.io/blog/parser-combinators-in-haskell
-- https://gist.github.com/heitor-lassarote/3e7314956e86b8227f6f6040e69aca9d

import FOL.NV.Formula

import Mathlib.Control.Basic


set_option autoImplicit false


inductive Error (i e : Type) : Type
  | EndOfInput : Error i e
  | ExpectedEndOfFile : i → Error i e
  | Expected : i → i → Error i e
  | Custom : e → Error i e
  deriving BEq, Repr

open Error


abbrev Offset : Type := Int


/--
  i : The input stream. For most cases this is going to be Char.
  e : The type of custom error messages.
  a : The type of the structure parsed from the consumed input.
--/
def Parser (i e a : Type) : Type :=
  List i → Offset →
    Except (List (Offset × Error i e)) (Offset × a × List i)


instance (i e : Type) : Functor (Parser i e) := {
  map :=
    fun {α β : Type} (f : α → β) (p : Parser i e α) =>
      fun (input : List i) (offset : Offset) => do
        let (offset', output, rest) ← p input offset
        return (offset', f output, rest) }


instance (i e : Type) : Applicative (Parser i e) := {
  pure :=
    fun {α : Type} (a : α) =>
      fun (input : List i) (offset : Offset) => Except.ok (offset, a, input),

  seq :=
    fun {α β : Type} (f : Parser i e (α → β)) (p : Unit → Parser i e α) =>
      fun (input : List i) (offset : Offset) => do
        let (offset', f', rest) ← f input offset
        let (offset'', output, rest') ← (p ()) rest offset'
        return (offset'', f' output, rest') }


instance (i e : Type) : Monad (Parser i e) := {
  pure := pure

  bind :=
    fun {α β : Type} (p : Parser i e α) (k : α → Parser i e β) =>
      fun (input : List i) (offset : Offset) => do
        let (offset', output, rest) ← p input offset
        let p' : Parser i e β := k output
        p' rest offset' }


instance (i e : Type) [BEq i] [BEq e] : Alternative (Parser i e) := {
  failure := fun (_ : List i) (_ : Offset) => Except.error []

  orElse := fun {α : Type} (l : Parser i e α) (r : Unit → Parser i e α) =>
    fun (input : List i) (offset : Offset) =>
      match l input offset with
      | Except.error err =>
          match (r ()) input offset with
          | Except.error err' =>
              Except.error (List.eraseDups (err ++ err'))
          | Except.ok result => Except.ok result
      | Except.ok result => Except.ok result }


def parse
  {i e a : Type}
  (p : Parser i e a)
  (input : List i) :
  Except (List (Offset × Error i e)) (Offset × a × List i) :=
  p input 0

def parseStr
  {e a : Type}
  (p : Parser Char e a)
  (input : String) :
  Except (List (Offset × Error Char e)) (Offset × a × List Char) :=
  parse p input.data


def eof
  (i e : Type) :
  Parser i e Unit :=
      fun (input : List i) (offset : Offset) =>
        match input with
        | [] => Except.ok (offset, (), [])
        | hd :: _ => Except.error [(offset, ExpectedEndOfFile hd)]


def satisfy
  {i e : Type}
  (mkErr : i → Error i e)
  (predicate : i → Bool) :
  Parser i e i :=
      fun (input : List i) (offset : Offset) =>
        match input with
        | [] => Except.error [(offset, EndOfInput)]
        | hd :: tl =>
            if predicate hd
            then Except.ok (offset + 1, hd, tl)
            else Except.error [(offset, mkErr hd)]


def exact_one
  {i : Type}
  [BEq i]
  (e : Type)
  (c : i) :
  Parser i e i :=
  satisfy (Expected c) (· == c)

def char
  (e : Type)
  (c : Char) :
  Parser Char e Char :=
  exact_one e c

#eval parseStr (char Unit 'a') ""
#eval parseStr (char Unit 'a') "a"
#eval parseStr (char Unit 'a') "b"


def exact_list
  {i : Type}
  [BEq i]
  (e : Type) :
  List i → Parser i e (List i)
  | [] => return []
  | x :: xs => do
    let y <- exact_one e x
    let ys <- exact_list e xs
    return (y :: ys)

def char_list
  (e : Type)
  (cs : List Char) :
  Parser Char e (List Char) :=
  exact_list e cs

def str
  (e : Type)
  (s : String) :
  Parser Char e String := do
  let cs ← char_list e s.data
  return cs.asString

#eval parseStr (str Unit "") ""
#eval parseStr (str Unit "") "a"
#eval parseStr (str Unit "a") "a"
#eval parseStr (str Unit "b") "a"
#eval parseStr (str Unit "ab") ""
#eval parseStr (str Unit "ab") "a"
#eval parseStr (str Unit "ab") "ab"
#eval parseStr (str Unit "ab") "ac"


def zero_or_one
  {i e a : Type}
  [BEq i]
  [BEq e]
  (p : Parser i e a) :
  Parser i e (Option a) := do
  try? p

def zero_or_one_char
  (e : Type)
  [BEq e]
  (c : Char) :
  Parser Char e String := do
  if let Option.some a ← zero_or_one (char e c)
  then return a.toString
  else return ""

#eval parseStr (zero_or_one_char Unit 'a') ""
#eval parseStr (zero_or_one_char Unit 'a') "b"
#eval parseStr (zero_or_one_char Unit 'a') "a"
#eval parseStr (zero_or_one_char Unit 'a') "ab"


partial def zero_or_more
  {i e a : Type}
  [BEq i]
  [BEq e]
  (p : Parser i e a) :
  Parser i e (Array a) := do
  let rec go (acc : Array a) := do
    match ← try? p with
    | none => return acc
    | some a => go (acc.push a)
  go #[]

def zero_or_more_char
  (e : Type)
  [BEq e]
  (c : Char) :
  Parser Char e String := do
  let a ← zero_or_more (char e c)
  return a.toList.asString

#eval parseStr (zero_or_more_char Unit 'a') ""
#eval parseStr (zero_or_more_char Unit 'a') "b"
#eval parseStr (zero_or_more_char Unit 'a') "bb"
#eval parseStr (zero_or_more_char Unit 'a') "a"
#eval parseStr (zero_or_more_char Unit 'a') "aa"
#eval parseStr (zero_or_more_char Unit 'a') "ab"
#eval parseStr (zero_or_more_char Unit 'a') "abb"


def one_or_more
  {i e a : Type}
  [BEq i]
  [BEq e]
  (p : Parser i e a) :
  Parser i e (Array a) := do
    let hd ← p
    let tl ← zero_or_more p
    return ⟨ hd :: tl.toList ⟩

def one_or_more_char
  (e : Type)
  [BEq e]
  (c : Char) :
  Parser Char e String := do
  let a ← one_or_more (char e c)
  return a.toList.asString

#eval parseStr (one_or_more_char Unit 'a') ""
#eval parseStr (one_or_more_char Unit 'a') "b"
#eval parseStr (one_or_more_char Unit 'a') "bb"
#eval parseStr (one_or_more_char Unit 'a') "a"
#eval parseStr (one_or_more_char Unit 'a') "aa"
#eval parseStr (one_or_more_char Unit 'a') "ab"
#eval parseStr (one_or_more_char Unit 'a') "aab"


#eval parseStr (char Unit 'a' <|> char Unit 'b') "a"
#eval parseStr (char Unit 'a' <|> char Unit 'b') "b"
#eval parseStr (char Unit 'a' <|> char Unit 'b') "c"

#eval parseStr ((failure <|> pure ()) : Parser Char Unit Unit) ""
#eval parseStr ((pure () <|> failure) : Parser Char Unit Unit) ""


def one_or_more_delimited
  {i e a1 a2 : Type}
  [BEq i]
  [BEq e]
  (delimiter : Parser i e a1)
  (p : Parser i e a2) :
  Parser i e (Array a2) := do
  let hd ← p
  let tl ← zero_or_more (delimiter *> p)
  return ⟨ hd :: tl.toList ⟩

def zero_or_more_delimited
  {i e a1 a2 : Type}
  [BEq i]
  [BEq e]
  (delimiter : Parser i e a1)
  (p : Parser i e a2) := do
  if let Option.some a ← zero_or_one (one_or_more_delimited delimiter p)
  then return a
  else return #[]


def whitespace :=
  satisfy (fun (c : Char) => Custom s! "Expected whitespace. Found '{c}'.") Char.isWhitespace

def alpha :=
  satisfy (fun (c : Char) => Custom s! "Expected alpha. Found '{c}'.") Char.isAlpha

def digit :=
  satisfy (fun (c : Char) => Custom s! "Expected digit. Found '{c}'.") Char.isDigit


def name := do
  let hd ← alpha <|> char String '_'
  let tl ← zero_or_more (alpha <|> digit <|> char String '_')
  return (Array.toList ⟨ hd :: tl.toList ⟩ ).asString

#eval parseStr name "_abc_0"


#eval parseStr (zero_or_more_delimited ((zero_or_more whitespace) *> char String ',' *> (zero_or_more whitespace)) name) "a , b , c"


open FOL.NV


def takePred := do
  let pred_name ← name
  _ ← zero_or_more whitespace
  _ ← char String '('
  _ ← zero_or_more whitespace
  let delimiter := zero_or_more whitespace *> char String ',' *> zero_or_more whitespace
  let xs ← zero_or_more_delimited delimiter name
  _ ← zero_or_more whitespace
  _ ← char String ')'

  return Formula.pred_var_ (PredName.mk pred_name) (xs.toList.map (VarName.mk ∘ toString))

#eval parseStr takePred "P()"
#eval parseStr takePred "P(x)"
#eval parseStr takePred "P(x, y)"


def takeEq := do
  _ ← zero_or_more whitespace
  _ ← char String '('
  _ ← zero_or_more whitespace
  let x ← name
  _ ← zero_or_more whitespace
  _ ← char String '='
  _ ← zero_or_more whitespace
  let y ← name
  _ ← zero_or_more whitespace
  _ ← char String ')'

  return Formula.eq_ (VarName.mk x) (VarName.mk y)

#eval parseStr takeEq "(x = y)"


def takeTrue := do
  _ ← str String "T."
  return Formula.true_

#eval parseStr takeTrue "T."


def takeFalse := do
  _ ← str String "F."
  return Formula.false_

#eval parseStr takeFalse "F."


mutual
  partial def takeFormula := do
    takeParen <|>
    takePred <|>
    takeEq <|>
    takeTrue <|>
    takeFalse <|>
    takeNot <|>
    takeBin <|>
    takeForall <|>
    takeExists


  partial def takeParen := do
    _ ← char String '('
    _ ← zero_or_more whitespace
    let phi ← takeFormula
    _ ← zero_or_more whitespace
    _ ← char String ')'

    return phi


  partial def takeNot := do
    _ ← char String '~'
    _ ← zero_or_more whitespace
    let phi ← takeFormula

    return (Formula.not_ phi)


  partial def takeBin := do
    _ ← char String '('
    _ ← zero_or_more whitespace
    let phi ← takeFormula
    _ ← zero_or_more whitespace
    let op ←
      (str String "->" *> pure Formula.imp_) <|>
      (str String "/\\" *> pure Formula.and_) <|>
      (str String "\\/" *> pure Formula.or_) <|>
      (str String "<->" *> pure Formula.iff_)
    _ ← zero_or_more whitespace
    let psi ← takeFormula
    _ ← zero_or_more whitespace
    _ ← char String ')'
    return op phi psi


  partial def takeForall := do
    _ ← str String "A."
    _ ← zero_or_more whitespace
    let x ← name
    _ ← zero_or_more whitespace
    let phi ← takeFormula

    return Formula.forall_ (VarName.mk x) phi


  partial def takeExists := do
    _ ← str String "E."
    _ ← zero_or_more whitespace
    let x ← name
    _ ← zero_or_more whitespace
    let phi ← takeFormula

    return Formula.exists_ (VarName.mk x) phi
end


#eval parseStr takeFormula "P()"
#eval parseStr takeFormula "P(x)"
#eval parseStr takeFormula "P(x, y)"
#eval parseStr takeFormula "A. x ~ (~ (P(x, y) -> P(x)))"
