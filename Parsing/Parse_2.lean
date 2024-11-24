import FOL.NV.Program.Sandbox.Editor

import Batteries.Data.String.Basic
import Mathlib.Control.Basic


set_option autoImplicit false


def isAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

def isAlphaOrDigit (c : Char) : Bool :=
  isAlpha c || isDigit c


abbrev Parser := ReaderT String <| StateT String.Pos Option

def Parser.run
  {α : Type}
  (p : Parser α)
  (s : String) :
  Option α :=
  (·.1) <$> p s 0


def matchEOF :
  Parser Unit :=
  fun (s : String) (pos : String.Pos) =>
  guard (pos == s.endPos) *> pure ((), pos)


def matchExactChar
  (c : Char) :
  Parser Unit :=
  fun (s : String) (pos : String.Pos) =>
  guard (pos < s.endPos && s.get pos == c) *> pure ((), s.next pos)

def matchExactString
  (token : String) :
  Parser Unit :=
  fun s pos => do
  let s ← Substring.dropPrefix? ⟨s, pos, s.endPos⟩ token.toSubstring
  pure ((), s.startPos)


-- one
def takeCharIf
  (f : Char → Bool) :
  Parser Char :=
  fun (s : String) (pos : String.Pos) =>
  let c := s.get pos
  if f c
  then pure (c, s.next pos)
  else none


-- zero or more
partial def takeWhile
  (f : Char → Bool) :
  Parser String :=
  fun (s : String) (start : String.Pos) =>
  let rec go pos :=
    if pos < s.endPos && f (s.get pos)
    then go (s.next pos)
    else pure (s.extract start pos, pos)
  go start


-- one or more
def takeWhile1
  (f : Char → Bool) :
  Parser String := do
  let s ← takeWhile f
  if s.isEmpty
  then none
  else pure s


-- Runs a single parser repeatedly until it fails.
partial def many
  {α : Type}
  (p : Parser α) :
  Parser (Array α) := do
  let rec go (acc : Array α) := do
    match ← try? p with
    | none => pure acc
    | some a => go (acc.push a)
  go #[]

-----

def takeIdent :
  Parser String := do
  let hd ← takeCharIf isAlpha
  let tl ← takeWhile (fun c : Char => isAlphaOrDigit c || c == '_' || c = '\'')
  pure (hd.toString ++ tl)

def takeIdentList :
  Parser (List String) := do
    {
      matchExactString "()";
      pure []
    } <|> do
    {
      matchExactChar '(';
      let hd ← takeIdent;
      let tl ← many (matchExactString ", " *> takeIdent);
      matchExactChar ')';
      pure (hd :: tl.toList)
    }

def takePred : Parser Formula := do
  let X ← takeIdent
  let xs ← takeIdentList
  pure (Formula.pred_var_ X xs)

def takeTrue : Parser Formula := do
  matchExactChar 'T'
  pure (Formula.true_)

def takeFalse : Parser Formula := do
  matchExactChar 'F'
  pure (Formula.false_)

mutual
  partial def takeFormula :
    Parser Formula :=
    takePred <|>
    takeTrue <|>
    takeFalse <|>
    takeNot <|>
    takeImp

  partial def takeNot : Parser Formula := do
    matchExactString "~ "
    let phi ← takeFormula
    pure (Formula.not_ phi)

  partial def takeImp : Parser Formula := do
    matchExactChar '('
    let phi ← takeFormula
    matchExactString " -> "
    let psi ← takeFormula
    matchExactChar ')'
    pure (Formula.imp_ phi psi)
end


def takeLabel :
  Parser String :=
  takeWhile1 (fun c : Char => isAlphaOrDigit c || c == '_' || c = '\'')


def takeFormulaList :
  Parser (List Formula) := do
    {
      matchExactString "[]";
      pure []
    } <|> do
    {
      matchExactChar '[';
      let hd ← takeFormula;
      let tl ← many (matchExactString ", " *> takeFormula);
      matchExactChar ']';
      pure (hd :: tl.toList)
    }


def takeThin :
  Parser Justification := do
  matchExactString "thin"
  matchExactChar ' '
  let label ← takeLabel
  matchExactChar ' '
  let xs ← takeFormulaList
  pure (Justification.thin_ label xs)

def takeAssume :
  Parser Justification := do
  matchExactString "assume"
  matchExactChar ' '
  let x ← takeFormula
  pure (Justification.assume_ x)

def takePropTrue :
  Parser Justification := do
  matchExactString "prop_true"
  pure Justification.prop_true_

def takeProp1 :
  Parser Justification := do
  matchExactString "prop_1"
  matchExactChar ' '
  let phi ← takeFormula
  matchExactChar ' '
  let psi ← takeFormula
  pure (Justification.prop_1_ phi psi)

def takeProp2 :
  Parser Justification := do
  matchExactString "prop_2"
  matchExactChar ' '
  let phi ← takeFormula
  matchExactChar ' '
  let psi ← takeFormula
  matchExactChar ' '
  let chi ← takeFormula
  pure (Justification.prop_2_ phi psi chi)

def takeProp3 :
  Parser Justification := do
  matchExactString "prop_3"
  matchExactChar ' '
  let phi ← takeFormula
  matchExactChar ' '
  let psi ← takeFormula
  pure (Justification.prop_3_ phi psi)

def takeMP :
  Parser Justification := do
  matchExactString "mp"
  matchExactChar ' '
  let major_step_label ← takeLabel
  matchExactChar ' '
  let minor_step_label ← takeLabel
  pure (Justification.mp_ major_step_label minor_step_label)

def takeJustification :
  Parser Justification :=
  takeThin <|>
  takeAssume <|>
  takePropTrue <|>
  takeProp1 <|>
  takeProp2 <|>
  takeProp3 <|>
  takeMP

def takeLabeledJustification :
  Parser (String × Justification) := do
  let label ← takeLabel
  matchExactChar '.'
  matchExactChar ' '
  let justification ← takeJustification
  pure (label, justification)

def takeLabeledJustificationList :
  Parser (List (String × Justification)) := do
  let hd ← takeLabeledJustification
  let tl ← many (matchExactString "; " *> takeLabeledJustification)
  pure (hd :: tl.toList)


def takeLabeledLabeledJustificationList :
  Parser (String × (List (String × Justification))) := do
  let label ← takeLabel
  matchExactChar '.'
  matchExactChar ' '
  let labeled_justification_list ← takeLabeledJustificationList
  pure (label, labeled_justification_list)


def takeLabeledLabeledJustificationListList :
  Parser (List (String × (List (String × Justification)))) := do
  let hd ← takeLabeledLabeledJustificationList
  matchExactChar LF
  let tl ← many (matchExactChar LF *> takeLabeledLabeledJustificationList)
  pure (hd :: tl.toList)


def checkProofList
  (s : String) :
  Except String (Array Proof) :=
  if let Option.some labeled_labeled_justification_list_list := takeLabeledLabeledJustificationListList.run s
  then createProofList labeled_labeled_justification_list_list
  else Except.error "Parsing error"


#eval checkProofList "id. 1. prop_2 P() (P() -> P()) P(); 2. prop_1 P() (P() -> P()); 3. mp 1 2; 4. prop_1 P() P(); 5. mp 3 4

id. 1. prop_2 P() (P() -> P()) P(); 2. prop_1 P() (P() -> P()); 3. mp 1 2; 4. prop_1 P() P(); 5. mp 3 4
"
