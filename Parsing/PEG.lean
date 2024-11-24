/-
  [1] https://bford.info/pub/lang/peg.pdf

  https://github.com/jayhardee9/peg-formalization/blob/master/peg.v
-/

import Batteries
import Mathlib.Util.CompileInductive

import Mathlib.Data.Finset.Basic


set_option autoImplicit false


/--
  The definition of parsing expressions.

  V_N is a finite set of nonterminal symbols.
  V_T is a finite set of terminal symbols.
-/
inductive PE (V_N V_T : Type) : Type
  | empty : PE V_N V_T
  | terminal : V_T → PE V_N V_T
  | nonTerminal : V_N → PE V_N V_T
  | seq : PE V_N V_T → PE V_N V_T → PE V_N V_T
  | choice : PE V_N V_T → PE V_N V_T → PE V_N V_T
  | star : PE V_N V_T → PE V_N V_T
  | notP : PE V_N V_T → PE V_N V_T
  deriving Inhabited, DecidableEq

compile_inductive% PE

open PE


/--
  The interpretation of a grammar.

  V_N is a finite set of nonterminal symbols.
  V_T is a finite set of terminal symbols.
  R is a finite set of rules.

  Section 3.3 of [1]:
  "Definition: To formalize the syntactic meaning of a grammar G = (V_N, V_T, R, eS), we define a relation ⇒G from pairs of the form (e, x) to pairs of the form (n, o), where e is a parsing expression, x ∈ V_T* is an input string to be recognized, n ≥ 0 serves as a “step counter,” and o ∈ V_T* ∪ { f } indicates the result of a recognition attempt. The “output” o of a successful match is the portion of the input string recognized and “consumed,” while a distinguished symbol f ∉ V_T indicates failure. For ((e, x), (n, o)) ∈ ⇒G we will write (e, x) ⇒ (n, o), with the reference to G being implied. We define ⇒G inductively as follows:"

  V_T* is translated as `List V_T`.
  V_T* ∪ { f } is translated as `Option (List V_T)`.
-/
inductive Interpretation
  (V_N V_T : Type)
  (R : V_N → PE V_N V_T) :
  (PE V_N V_T × List V_T) → (Nat × Option (List V_T)) → Prop

    /-
      Empty
    -/
  | empty
    (xs : List V_T) :
    Interpretation V_N V_T R (empty, xs) (1, Option.some [])

    /-
      Terminal (success case)
    -/
  | terminal_success
    (a : V_T)
    (xs : List V_T) :
    Interpretation V_N V_T R (terminal a, a :: xs) (1, Option.some [a])

    /-
      Terminal (failure case)
    -/
  | terminal_failure_1
    (a b : V_T)
    (xs : List V_T) :
    ¬ a = b →
    Interpretation V_N V_T R (terminal a, b :: xs) (1, Option.none)

    /-
      Terminal (failure case)
    -/
  | terminal_failure_2
    (a : V_T)
    (xs : List V_T) :
    Interpretation V_N V_T R (terminal a, []) (1, Option.none)

    /-
      Nonterminal
    -/
  | nonTerminal
    (A : V_N)
    (xs : List V_T)
    (n : Nat)
    (o : Option (List V_T)) :
    Interpretation V_N V_T R (R A, xs) (n, o) →
    Interpretation V_N V_T R (nonTerminal A, xs) (n + 1, o)

    /-
      Sequence (success case)

      Expressions e1 and e2 are matched in sequence, and if each succeeds and consumes input portions x1 and x2 respectively, then the sequence succeeds and consumes the string x1 x2.
    -/
  | seq_success
    (e1 e2 : PE V_N V_T)
    (xs_1 xs_2 ys : List V_T)
    (n1 n2 : Nat) :
    Interpretation V_N V_T R (e1, xs_1 ++ xs_2 ++ ys) (n1, Option.some xs_1) →
    Interpretation V_N V_T R (e2, xs_2 ++ ys) (n2, Option.some xs_2) →
    Interpretation V_N V_T R (seq e1 e2, xs_1 ++ xs_2 ++ ys) (n1 + n2 + 1, Option.some (xs_1 ++ xs_2))

    /-
      Sequence (failure case 1)

      If e1 is tested and fails, then the sequence e1 e2 fails without attempting e2.
    -/
  | seq_failure_1
    (e1 e2 : PE V_N V_T)
    (xs : List V_T)
    (n : Nat) :
    Interpretation V_N V_T R (e1, xs) (n, Option.none) →
    Interpretation V_N V_T R (seq e1 e2, xs) (n + 1, Option.none)

    /-
      Sequence (failure case 2)

      If e1 succeeds but e2 fails, then the sequence expression fails.
    -/
  | seq_failure_2
    (e1 e2 : PE V_N V_T)
    (xs ys : List V_T)
    (n1 n2 : Nat) :
    Interpretation V_N V_T R (e1, xs ++ ys) (n1, Option.some xs) →
    Interpretation V_N V_T R (e2, ys) (n2, Option.none) →
    Interpretation V_N V_T R (seq e1 e2, xs ++ ys) (n1 + n2 + 1, Option.none)

    /-
      Alternation (case 1)

      Alternative e1 is first tested, and if it succeeds, the expression e1/e2 succeeds without testing e2.
    -/
  | choice_1
    (e1 e2 : PE V_N V_T)
    (xs ys : List V_T)
    (n : Nat) :
    Interpretation V_N V_T R (e1, xs ++ ys) (n, Option.some xs) →
    Interpretation V_N V_T R (choice e1 e2, xs ++ ys) (n + 1, Option.some xs)

    /-
      Alternation (case 2)

      If e1 fails, then e2 is tested and its result is used instead.
    -/
  | choice_2
    (e1 e2 : PE V_N V_T)
    (xs : List V_T)
    (n1 n2 : Nat)
    (o : Option (List V_T)) :
    Interpretation V_N V_T R (e1, xs) (n1, Option.none) →
    Interpretation V_N V_T R (e2, xs) (n2, o) →
    Interpretation V_N V_T R (choice e1 e2, xs) (n1 + n2 + 1, o)

    /-
      Zero-or-more repetitions (repetition case)
    -/
  | star_repetition
    (e : PE V_N V_T)
    (xs_1 xs_2 ys : List V_T)
    (n1 n2 : Nat) :
    Interpretation V_N V_T R (e, xs_1 ++ xs_2 ++ ys) (n1, Option.some xs_1) →
    Interpretation V_N V_T R (star e, xs_2 ++ ys) (n2, Option.some xs_2) →
    Interpretation V_N V_T R (star e, xs_1 ++ xs_2 ++ ys) (n1 + n2 + 1, Option.some (xs_1 ++ xs_2))

    /-
      Zero-or-more repetitions (termination case)
    -/
  | star_termination
    (e : PE V_N V_T)
    (xs : List V_T)
    (n : Nat) :
    Interpretation V_N V_T R (e, xs) (n, Option.none) →
    Interpretation V_N V_T R (star e, xs) (n + 1, Option.some [])

    /-
      Not-predicate (case 1)

      If expression e succeeds consuming input x, then the syntactic predicate !e fails.
    -/
  | notP_1
    (e : PE V_N V_T)
    (xs ys : List V_T)
    (n : Nat) :
    Interpretation V_N V_T R (e, xs ++ ys) (n, Option.some xs) →
    Interpretation V_N V_T R (notP e, xs ++ ys) (n + 1, Option.none)

    /-
      Not-predicate (case 2)

      If e fails, then !e succeeds but consumes nothing.
    -/
  | notP_2
    (e : PE V_N V_T)
    (xs : List V_T)
    (n : Nat) :
    Interpretation V_N V_T R (e, xs) (n, Option.none) →
    Interpretation V_N V_T R (notP e, xs) (n + 1, Option.some [])


lemma InterpretationEmpty
  (V_N V_T : Type)
  (R : V_N → PE V_N V_T)
  (n : ℕ)
  (xs : List V_T)
  (o : Option (List V_T))
  (h1 : Interpretation V_N V_T R (empty, xs) (n, o)) :
  n = 1 ∧ o = (Option.some []) :=
  by
  cases h1
  simp


lemma InterpretationSteps
  (V_N V_T : Type)
  (R : V_N → PE V_N V_T)
  (e : PE V_N V_T)
  (xs : List V_T)
  (o : Option (List V_T))
  (n : Nat)
  (h1 : Interpretation V_N V_T R (e, xs) (n, o)) :
  n > 0 :=
  by
  cases h1
  all_goals
    omega


lemma EmptyStringPrefix
  (α : Type)
  (xs : List α) :
  List.IsPrefix [] xs :=
  by
  exact List.nil_prefix


lemma CharPrefix
  (α : Type)
  (x : α)
  (xs : List α) :
  List.IsPrefix [x] (x :: xs) :=
  by
  exact List.prefix_iff_eq_take.mpr rfl


lemma PrefixAppend
  (α : Type)
  (xs ys : List α) :
  List.IsPrefix xs (xs ++ ys) :=
  by
  exact List.prefix_append xs ys


/-
  Theorem: If (e, x) ⇒ (n, y), then y is a prefix of x: ∃z(x = yz).
-/
theorem InterpretationPrefix
  (V_N V_T : Type)
  (R : V_N → PE V_N V_T)
  (e : PE V_N V_T)
  (xs ys : List V_T)
  (n : Nat)
  (h1 : Interpretation V_N V_T R (e, xs) (n, Option.some ys)) :
  List.IsPrefix ys xs :=
  by
  induction n using Nat.strongInductionOn generalizing e
  case ind n ih =>
  cases h1
  any_goals
    first | apply EmptyStringPrefix | apply CharPrefix | apply PrefixAppend
  case nonTerminal A n ih_1 =>
    specialize ih n _ (R A)
    · omega
    · exact ih ih_1
  case choice_2 e1 e2 n1 n2 ih_1 ih_2 =>
    specialize ih n2 _ e2
    · omega
    · exact ih ih_2


example
  (V_N V_T : Type)
  (R : V_N → PE V_N V_T)
  (e : PE V_N V_T)
  (xs : List V_T)
  (n1 n2 : Nat)
  (o1 o2 : Option (List V_T))
  (h1 : Interpretation V_N V_T R (e, xs) (n1, o1))
  (h2 : Interpretation V_N V_T R (e, xs) (n2, o2)) :
  n1 = n2 ∧ o1 = o2 :=
  by
  induction n1 using Nat.strongInductionOn generalizing e n2
  case ind n1 ih_n1 =>
    induction n2 using Nat.strongInductionOn generalizing e n1
    case ind n2 ih_n2 =>
      induction e generalizing n1 n2
      case empty =>
        cases h1
        cases h2
        simp
      case terminal =>
        cases h1
        all_goals
          cases h2
          all_goals
            first | contradiction | simp only [and_self]
      case nonTerminal A =>
        cases h1
        cases h2
        case nonTerminal.nonTerminal n1 ih_1 n2 ih_2 =>
          simp
          apply ih_n1 n1 _ (R A) n2 ih_1 ih_2
          omega
      case seq e1 e2 ih_1 ih_2 =>
        sorry
      all_goals
        sorry


inductive O : Type
  | zero : O
  | one : O
  | f : O


inductive relation
  (V_N V_T : Type)
  (R : V_N → PE V_N V_T) :
  PE V_N V_T → O → Prop

  | empty_ :
    relation V_N V_T R PE.empty O.zero

  | terminal_1
    (a : V_T) :
    relation V_N V_T R (PE.terminal a) O.one

  | terminal_2
    (a : V_T) :
    relation V_N V_T R (PE.terminal a) O.f

  | nonTerminal
    (A : V_N)
    (o : O) :
    relation V_N V_T R (R A) o →
    relation V_N V_T R (nonTerminal A) o

  | seq_success_zero_zero
    (e1 e2 : PE V_N V_T) :
    relation V_N V_T R e1 O.zero →
    relation V_N V_T R e2 O.zero →
    relation V_N V_T R (seq e1 e2) O.zero

  | seq_success_one_zero
    (e1 e2 : PE V_N V_T) :
    relation V_N V_T R e1 O.one →
    relation V_N V_T R e2 O.zero →
    relation V_N V_T R (seq e1 e2) O.one

  | seq_success_zero_one
    (e1 e2 : PE V_N V_T) :
    relation V_N V_T R e1 O.zero →
    relation V_N V_T R e2 O.one →
    relation V_N V_T R (seq e1 e2) O.one

  | seq_success_one_one
    (e1 e2 : PE V_N V_T) :
    relation V_N V_T R e1 O.one →
    relation V_N V_T R e2 O.one →
    relation V_N V_T R (seq e1 e2) O.one

  | seq_failure_1
    (e1 e2 : PE V_N V_T) :
    relation V_N V_T R e1 O.f →
    relation V_N V_T R (seq e1 e2) O.f

  | seq_failure_2
    (e1 e2 : PE V_N V_T) :
    relation V_N V_T R e1 O.zero →
    relation V_N V_T R e2 O.f →
    relation V_N V_T R (seq e1 e2) O.f

  | seq_failure_3
    (e1 e2 : PE V_N V_T) :
    relation V_N V_T R e1 O.one →
    relation V_N V_T R e2 O.f →
    relation V_N V_T R (seq e1 e2) O.f


--#lint
