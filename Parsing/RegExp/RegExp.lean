import FOL.Parsing.EpsilonNFA


set_option autoImplicit false


def EpsilonNFA.wrapLeft
  {α : Type}
  {σ_l : Type}
  (σ_r : Type)
  (M : EpsilonNFA α σ_l) :
  EpsilonNFA α (σ_l ⊕ σ_r) :=
  M.map Sum.inl


def EpsilonNFA.wrapRight
  {α : Type}
  (σ_l : Type)
  {σ_r : Type}
  (M : EpsilonNFA α σ_r) :
  EpsilonNFA α (σ_l ⊕ σ_r) :=
  M.map Sum.inr

-------------------------------------------------------------------------------

def match_char_EpsilonNFA
  {α : Type}
  (c : α) :
  EpsilonNFA α ℕ :=
  {
    symbol_arrow_list := [⟨0, c, [1]⟩]
    epsilon_arrow_list := []
    starting_state_list := [0]
    accepting_state_list := [1]
  }

def match_char_AbstractEpsilonNFA
  {α : Type}
  [DecidableEq α]
  (c : α) :
  AbstractEpsilonNFA α ℕ :=
    {
      symbol := fun p a q => p = 0 ∧ a = c ∧ q = 1
      epsilon := fun _ _ => False
      start := fun p => p = 0
      accepting := fun p => p = 1
    }

theorem match_char_EpsilonNFA_toAbstract
  {α : Type}
  [DecidableEq α]
  (c : α) :
  (match_char_EpsilonNFA c).toAbstract =
    match_char_AbstractEpsilonNFA c :=
  by
    simp only [match_char_EpsilonNFA]
    simp only [EpsilonNFA.toAbstract]
    simp only [match_char_AbstractEpsilonNFA]
    simp
    simp only [← and_assoc]
    simp only [and_right_comm]
    simp


example : (match_char_EpsilonNFA 'a').eval [] = [0] := by with_unfolding_all rfl
example : (match_char_EpsilonNFA 'a').eval ['a'] = [1] := by with_unfolding_all rfl
example : (match_char_EpsilonNFA 'a').eval ['b'] = [] := by with_unfolding_all rfl
example : (match_char_EpsilonNFA 'a').eval ['a', 'b'] = [] := by with_unfolding_all rfl
example : (match_char_EpsilonNFA 'a').eval ['b', 'a'] = [] := by with_unfolding_all rfl


example : ¬ (match_char_EpsilonNFA 'a').accepts [] :=
  by with_unfolding_all decide


example : (match_char_EpsilonNFA 'a').accepts ['a'] :=
  by with_unfolding_all decide

example : ¬ (match_char_EpsilonNFA 'a').accepts ['b'] :=
  by with_unfolding_all decide


example : ¬ (match_char_EpsilonNFA 'a').accepts ['a', 'b'] :=
  by with_unfolding_all decide


example : ¬ (match_char_EpsilonNFA 'a').accepts ['b', 'a'] :=
  by with_unfolding_all decide


example
  (α : Type)
  [DecidableEq α]
  (c : α)
  (x : α) :
  (match_char_EpsilonNFA c).accepts [x] ↔ x = c :=
  by
    simp only [EpsilonNFA.accepts_iff]
    simp only [match_char_EpsilonNFA_toAbstract]
    simp only [match_char_AbstractEpsilonNFA]
    simp only [AbstractEpsilonNFA.accepts]
    simp
    constructor
    · intro a1
      cases a1
      case _ stop_state ih_1 ih_2 =>
        simp only at ih_1
      case _ stop_state ih_1 ih_2 =>
        simp only at ih_1
        tauto
    · intro a1
      apply AbstractEpsilonNFA.eval.sym 0 _ 1
      · apply AbstractEpsilonNFA.eval.accept
        simp only
      · simp only
        simp only [a1]
        simp


example
  (α : Type)
  [DecidableEq α]
  (c : α)
  (x y : α) :
  ¬ (match_char_EpsilonNFA c).accepts [x, y] :=
  by
    simp only [EpsilonNFA.accepts_iff]
    simp only [match_char_EpsilonNFA_toAbstract]
    simp only [match_char_AbstractEpsilonNFA]
    simp only [AbstractEpsilonNFA.accepts]
    simp
    intro contra
    cases contra
    case eps stop_state ih_1 ih_2 =>
      simp only at ih_1
    case sym stop_state ih_1 ih_2 =>
      simp only at ih_1
      simp at ih_1
      cases ih_1
      case _ ih_1_left ih_1_right =>
        subst ih_1_left
        subst ih_1_right
        cases ih_2
        case eps stop_state ih_1 ih_2 =>
          simp only at ih_1
        case sym stop_state ih_1 ih_2 =>
          simp only at ih_1
          simp at ih_1

-------------------------------------------------------------------------------

def match_epsilon_EpsilonNFA
  (α : Type) :
  EpsilonNFA α ℕ :=
  {
    symbol_arrow_list := []
    epsilon_arrow_list := [⟨0, [1]⟩]
    starting_state_list := [0]
    accepting_state_list := [1]
  }

def match_epsilon_AbstractEpsilonNFA
  (α : Type)
  [DecidableEq α] :
  AbstractEpsilonNFA α ℕ :=
  {
    symbol := fun _ _ _ => False
    epsilon := fun p q => p = 0 ∧ q = 1
    start := fun p => p = 0
    accepting := fun p => p = 1
  }

theorem match_epsilon_EpsilonNFA_toAbstract
  {α : Type}
  [DecidableEq α] :
  (match_epsilon_EpsilonNFA α).toAbstract = match_epsilon_AbstractEpsilonNFA α :=
  by
    simp only [match_epsilon_EpsilonNFA]
    simp only [EpsilonNFA.toAbstract]
    simp only [match_epsilon_AbstractEpsilonNFA]
    simp
    funext p q
    simp
    constructor
    · intro a1

      apply Exists.elim a1
      intro stop_state_list a2
      clear a1

      cases a2
      case _ a2_left a2_right =>
        cases a2_left
        case _ a2_left_left a2_left_right =>
          simp only [a2_left_right] at a2_right
          simp at a2_right
          tauto
    · intro a1
      apply Exists.intro [1]
      simp
      exact a1


example
  (α : Type)
  [DecidableEq α] :
  (match_epsilon_EpsilonNFA α).accepts [] :=
  by
    apply Exists.intro 1
    with_unfolding_all tauto

-------------------------------------------------------------------------------

def match_zero_EpsilonNFA
  (α : Type) :
  EpsilonNFA α ℕ :=
  {
    symbol_arrow_list := []
    epsilon_arrow_list := []
    starting_state_list := [0]
    accepting_state_list := []
  }

def match_zero_AbstractEpsilonNFA
  (α : Type) :
  AbstractEpsilonNFA α ℕ :=
  {
    symbol := fun _ _ _ => False
    epsilon := fun _ _ => False
    start := fun p => p = 0
    accepting := fun _ => False
  }

theorem match_zero_EpsilonNFA_toAbstract
  {α : Type}
  [DecidableEq α] :
  (match_zero_EpsilonNFA α).toAbstract = match_zero_AbstractEpsilonNFA α :=
  by
    simp only [match_zero_EpsilonNFA]
    simp only [EpsilonNFA.toAbstract]
    simp only [match_zero_AbstractEpsilonNFA]
    simp


example
  (α : Type)
  [DecidableEq α]
  (xs : List α) :
  ¬ (match_zero_EpsilonNFA α).accepts xs :=
  by
    simp only [EpsilonNFA.accepts_iff]
    simp only [match_zero_EpsilonNFA_toAbstract]
    simp only [AbstractEpsilonNFA.accepts]
    simp only [match_zero_AbstractEpsilonNFA]
    simp
    intro contra
    cases contra
    case eps stop_state ih_1 ih_2 =>
      simp only at ih_1
    case sym c stop_state cs ih_1 ih_2 =>
      simp only at ih_2
    case accept ih_1 =>
      simp only at ih_1

-------------------------------------------------------------------------------

def match_union_EpsilonNFA
  (α : Type)
  (σ_0 σ_1 : Type)
  (M_0 : EpsilonNFA α σ_0)
  (M_1 : EpsilonNFA α σ_1) :
  EpsilonNFA α (σ_0 ⊕ σ_1) :=
  let M_0' := M_0.wrapLeft σ_1
  let M_1' := M_1.wrapRight σ_0
  {
    symbol_arrow_list := M_0'.symbol_arrow_list ++ M_1'.symbol_arrow_list
    epsilon_arrow_list := M_0'.epsilon_arrow_list ++ M_1'.epsilon_arrow_list
    starting_state_list := M_0'.starting_state_list ++ M_1'.starting_state_list
    accepting_state_list := M_0'.accepting_state_list ++ M_1'.accepting_state_list
  }

def match_union_AbstractEpsilonNFA
  (α : Type)
  (σ_0 σ_1 : Type)
  (M_0 : AbstractEpsilonNFA α σ_0)
  (M_1 : AbstractEpsilonNFA α σ_1) :
  AbstractEpsilonNFA α (σ_0 ⊕ σ_1) :=
    {
      symbol := fun p c q =>
        match (p, q) with
        | (Sum.inl p', Sum.inl q') => M_0.symbol p' c q'
        | (Sum.inr p', Sum.inr q') => M_1.symbol p' c q'
        | _ => False,
      epsilon := fun p q =>
        match (p, q) with
        | (Sum.inl p', Sum.inl q') => M_0.epsilon p' q'
        | (Sum.inr p', Sum.inr q') => M_1.epsilon p' q'
        | _ => False,
      start := fun p =>
        match p with
        | Sum.inl p' => M_0.start p'
        | Sum.inr p' => M_1.start p'
      accepting := fun p =>
        match p with
        | Sum.inl p' => M_0.accepting p'
        | Sum.inr p' => M_1.accepting p'
    }

theorem match_union_EpsilonNFA_toAbstract
  {α : Type}
  [DecidableEq α]
  (σ_0 σ_1 : Type)
  (M_0 : EpsilonNFA α σ_0)
  (M_1 : EpsilonNFA α σ_1) :
  (match_union_EpsilonNFA α σ_0 σ_1 M_0 M_1).toAbstract =
    match_union_AbstractEpsilonNFA α σ_0 σ_1 M_0.toAbstract M_1.toAbstract :=
  by
    simp only [match_union_EpsilonNFA]
    simp only [EpsilonNFA.toAbstract]
    simp only [match_union_AbstractEpsilonNFA]
    simp only [AbstractEpsilonNFA.mk.injEq]
    simp only [EpsilonNFA.wrapLeft]
    simp only [EpsilonNFA.wrapRight]
    simp only [EpsilonNFA.map]
    constructor
    · funext p c q
      cases p
      case _ p_0 =>
        cases q
        case _ q_0 =>
          simp only [eq_iff_iff]
          constructor
          · simp
            intro xs x a1 a2 a3 a4 a5
            simp only [← a4] at a5
            clear a4
            simp only [← a2]
            simp only [← a3]
            apply Exists.intro x.stop_state_list
            constructor
            · exact a1
            · simp at a5
              exact a5
          · simp
            intro xs x a1
            apply Exists.intro (xs.map Sum.inl)
            constructor
            · apply Exists.intro { start_state := p_0, symbol := c, stop_state_list := xs }
              simp
              exact x
            · simp
              exact a1
        case _ q0 =>
          simp
          intro xs x _ _ _ a4
          simp only [← a4]
          simp
      case _ p0 =>
        cases q
        case _ q_0 =>
          simp only [eq_iff_iff]
          constructor
          · simp
            intro xs x _ _ _ a4
            simp only [← a4]
            simp
          · simp
        case _ q0 =>
          simp
          constructor
          · intro a1
            cases a1
            case _ xs a2 =>
              cases a2
              case _ a2_left a2_right =>
                cases a2_left
                case _ x a3 =>
                  cases a3
                  case _ a3_left a3_right =>
                    cases a3_right
                    case _ a3_right_left a3_right_right =>
                      cases a3_right_right
                      case _ a3_right_right_left a3_right_right_right =>
                        simp only [← a3_right_right_right] at a2_right
                        clear a3_right_right_right

                        simp only [← a3_right_left]
                        simp only [← a3_right_right_left]

                        simp at a2_right

                        apply Exists.intro x.stop_state_list
                        constructor
                        · exact a3_left
                        · exact a2_right
          · intro a1
            cases a1
            case _ xs a2 =>
              cases a2
              case _ a2_left a2_right =>
                apply Exists.intro (xs.map Sum.inr)
                constructor
                · apply Exists.intro { start_state := p0, symbol := c, stop_state_list := xs }
                  simp
                  exact a2_left
                · simp
                  exact a2_right
    · constructor
      · funext p q
        cases p
        case _ p_0 =>
          cases q
          case _ q_0 =>
            simp
            constructor
            · intro a1
              cases a1
              case _ xs a2 =>
                cases a2
                case _ a2_left a2_right =>
                  cases a2_left
                  case _ x a3 =>
                    cases a3
                    case _ a3_left a3_right =>
                      cases a3_right
                      case _ a3_right_left a3_right_right =>
                        simp only [← a3_right_right] at a2_right
                        clear a3_right_right
                        simp at a2_right

                        apply Exists.intro x.stop_state_list
                        simp only [← a3_right_left]
                        constructor
                        · exact a3_left
                        · exact a2_right
            · intro a1
              cases a1
              case _ xs a2 =>
                cases a2
                case _ a2_left a2_right =>
                  apply Exists.intro (xs.map Sum.inl)
                  constructor
                  · apply Exists.intro { start_state := p_0, stop_state_list := xs }
                    simp
                    exact a2_left
                  · simp
                    exact a2_right
          case _ q_0 =>
            simp
            intro xs x _ _ a3
            simp only [← a3]
            simp
        case _ p_0 =>
          cases q
          case _ q_0 =>
            simp
            intro xs x _ _ a3
            simp only [← a3]
            simp
          case _ q_0 =>
            simp
            constructor
            · intro a1
              cases a1
              case _ xs a2 =>
                cases a2
                case _ a2_left a2_right =>
                  cases a2_left
                  case _ x a3 =>
                    cases a3
                    case _ a3_left a3_right =>
                      cases a3_right
                      case _ a3_right_left a3_right_right =>
                        simp only [← a3_right_right] at a2_right
                        clear a3_right_right
                        simp at a2_right

                        apply Exists.intro x.stop_state_list
                        simp only [← a3_right_left]
                        constructor
                        · exact a3_left
                        · exact a2_right
            · intro a1
              cases a1
              case _ xs a2 =>
                cases a2
                case _ a2_left a2_right =>
                  apply Exists.intro (xs.map Sum.inr)
                  constructor
                  · apply Exists.intro { start_state := p_0, stop_state_list := xs }
                    simp
                    exact a2_left
                  · simp
                    exact a2_right
      · constructor
        · funext p
          cases p
          · simp
          · simp
        · funext p
          cases p
          · simp
          · simp


-------------------------------------------------------------------------------

def match_concat_EpsilonNFA
  (α : Type)
  (σ_0 σ_1 : Type)
  (M_0 : EpsilonNFA α σ_0)
  (M_1 : EpsilonNFA α σ_1) :
  EpsilonNFA α (ℕ ⊕ σ_0 ⊕ σ_1) :=
  let M_0' := (M_0.wrapLeft σ_1).wrapRight ℕ
  let M_1' := (M_1.wrapRight σ_0).wrapRight ℕ
  {
    symbol_arrow_list := M_0'.symbol_arrow_list ++ M_1'.symbol_arrow_list

    epsilon_arrow_list := M_0'.epsilon_arrow_list ++ M_1'.epsilon_arrow_list ++ M_0'.accepting_state_list.map (fun (accepting_state) => ⟨ accepting_state, M_1'.starting_state_list ⟩)

    starting_state_list := M_0'.starting_state_list
    accepting_state_list := M_1'.accepting_state_list
  }

def match_concat_AbstractEpsilonNFA
  (α : Type)
  (σ_0 σ_1 : Type)
  (M_0 : AbstractEpsilonNFA α σ_0)
  (M_1 : AbstractEpsilonNFA α σ_1) :
  AbstractEpsilonNFA α (ℕ ⊕ σ_0 ⊕ σ_1) :=
    {
      symbol := fun p c q =>
        match (p, q) with
        | (Sum.inr (Sum.inl p'), Sum.inr (Sum.inl q')) => M_0.symbol p' c q'
        | (Sum.inr (Sum.inr p'), Sum.inr (Sum.inr q')) => M_1.symbol p' c q'
        | _ => False,
      epsilon := fun p q =>
        match (p, q) with
        | (Sum.inr (Sum.inl p'), Sum.inr (Sum.inl q')) => M_0.epsilon p' q'
        | (Sum.inr (Sum.inr p'), Sum.inr (Sum.inr q')) => M_1.epsilon p' q'
        | (Sum.inr (Sum.inl p'), Sum.inr (Sum.inr q')) => M_0.accepting p' ∧ M_1.start q'
        | _ => False
      start := fun p =>
        match p with
        | Sum.inr (Sum.inl p') => M_0.start p'
        | _ => False
      accepting := fun p =>
        match p with
        | Sum.inr (Sum.inr p') => M_1.accepting p'
        | _ => False
    }


theorem match_concat_EpsilonNFA_toAbstract
  {α : Type}
  [DecidableEq α]
  (σ_0 σ_1 : Type)
  (M_0 : EpsilonNFA α σ_0)
  (M_1 : EpsilonNFA α σ_1) :
  (match_concat_EpsilonNFA α σ_0 σ_1 M_0 M_1).toAbstract =
    match_concat_AbstractEpsilonNFA α σ_0 σ_1 M_0.toAbstract M_1.toAbstract :=
  by
    simp only [match_concat_EpsilonNFA]
    simp only [EpsilonNFA.toAbstract]
    simp only [match_concat_AbstractEpsilonNFA]
    simp only [AbstractEpsilonNFA.mk.injEq]
    simp only [EpsilonNFA.wrapLeft]
    simp only [EpsilonNFA.wrapRight]
    simp only [EpsilonNFA.map]
    constructor
    · funext p c q
      cases p
      case _ p_0 =>
        simp
      case _ p_0 =>
        cases p_0
        case _ p_0 =>
          cases q
          case _ q_0 =>
            simp
            intro xs x a1 a2 a3 a4
            simp only [← a4]
            simp
          case _ q_0 =>
            cases q_0
            case _ q_0 =>
              simp
              sorry
            case _ q_0 =>
              simp
              intro xs x a1 a2 a3 a4
              simp only [← a4]
              simp
        case _ p_0 =>
          cases q
          case _ q_0 =>
            simp
            intro xs x a1 a2 a3 a4
            simp only [← a4]
            simp
          case _ q_0 =>
            cases q_0
            case _ q_0 =>
              simp
              intro xs x a1 a2 a3 a4
              simp only [← a4]
              simp
            case _ q_0 =>
              simp
              sorry
    · constructor
      · funext p q
        cases p
        case _ p_0 =>
          simp
        case _ p_0 =>
          cases p_0
          case _ p_0 =>
            cases q
            case _ q_0 =>
              simp
              intro xs a1
              cases a1
              case _ left =>
                cases left
                case _ x a2 =>
                  cases a2
                  case _ a2_left a2_right =>
                    cases a2_right
                    case _ a2_right_left a2_right_right =>
                      simp only [← a2_right_right]
                      simp
              case _ right =>
                cases right
                case _ x a2 =>
                  cases a2
                  case _ a2_left a2_right =>
                    cases a2_right
                    case _ a2_right_left a2_right_right =>
                      simp only [← a2_right_right]
                      simp
            case _ q_0 =>
              cases q_0
              case _ q_0 =>
                simp
                sorry
              case _ q_0 =>
                simp
                sorry
          case _ p_0 =>
            cases q
            case _ q_0 =>
              simp
              intro xs x a1 a2 a3
              simp only [← a3]
              simp
            case _ q_0 =>
              cases q_0
              case _ q_0 =>
                simp
                intro xs x a1 a2 a3
                simp only [← a3]
                simp
              case _ q_0 =>
                simp
                sorry
      · constructor
        · funext p
          cases p
          case _ p_0 =>
            simp
          case _ p_0 =>
            cases p_0
            case _ p_0 =>
              simp
            case _ p_0 =>
              simp
        · funext p
          cases p
          case _ p_0 =>
            simp
          case _ p_0 =>
            cases p_0
            case _ p_0 =>
              simp
            case _ p_0 =>
              simp


-------------------------------------------------------------------------------


inductive RegExp
  (α : Type) :
  Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | closure : RegExp α → RegExp α
  deriving Repr

compile_inductive% RegExp


@[reducible]
def RegExp.State
  (α : Type) :
  RegExp α → Type
| char _ => ℕ
| epsilon => ℕ
| zero => ℕ
| union R S => R.State ⊕ S.State
| concat R S => (ℕ ⊕ R.State ⊕ S.State)
| closure R => Option R.State


def RegExp.toEpsilonNFA
  {α : Type}
  (E : RegExp α) :
  EpsilonNFA α E.State :=
  match E with
  | char c => match_char_EpsilonNFA c

  | epsilon => match_epsilon_EpsilonNFA α

  | zero => match_zero_EpsilonNFA α

  | union R S => match_union_EpsilonNFA α R.State S.State R.toEpsilonNFA S.toEpsilonNFA

  | concat R S => match_concat_EpsilonNFA α R.State S.State R.toEpsilonNFA S.toEpsilonNFA

  | closure R => sorry


def RegExp.toAbstractEpsilonNFA
  {α : Type}
  [DecidableEq α]
  (E : RegExp α) :
  AbstractEpsilonNFA α E.State :=
  match E with
  | char c => match_char_AbstractEpsilonNFA c

  | epsilon => match_epsilon_AbstractEpsilonNFA α

  | zero => match_zero_AbstractEpsilonNFA α

  | union R S => match_union_AbstractEpsilonNFA α R.State S.State R.toAbstractEpsilonNFA S.toAbstractEpsilonNFA

  | concat R S => match_concat_AbstractEpsilonNFA α R.State S.State R.toAbstractEpsilonNFA S.toAbstractEpsilonNFA

  | closure R => sorry


-------------------------------------------------------------------------------

/-
def match_closure_EpsilonNFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ]
  (e : EpsilonNFA α σ) :
  EpsilonNFA α (ℕ ⊕ σ) :=

  let e' : EpsilonNFA α (ℕ ⊕ σ) := e.wrapRight ℕ

  let new_starting_state : ℕ ⊕ σ := Sum.inl 0

  -- A step on epsilon from the new starting state to the starting state of e'.
  let new_starting_step : ((ℕ ⊕ σ) × Option α) × List (ℕ ⊕ σ) := ((new_starting_state, Option.none), e'.startingStateList)

  -- Steps on epsilon from each of the accepting states of e' to the new starting state.
  let new_step_list := e'.acceptingStateList.map (fun (state : ℕ ⊕ σ) => ((state, Option.none), [new_starting_state]))

  {
/-
    stateSet := {new_starting_state} ∪ e'.stateSet
    symbolSet := e'.symbolSet
-/
    stepList := new_starting_step :: new_step_list
    startingStateList := [new_starting_state]
    acceptingStateList := new_starting_state :: e'.acceptingStateList
  }
-/
