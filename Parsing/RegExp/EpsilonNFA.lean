import FOL.Parsing.DFT


set_option autoImplicit false


structure SymbolArrow
  (α : Type)
  (σ : Type) :
  Type :=
  (start_state : σ)
  (symbol : α)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonArrow
  (σ : Type) :
  Type :=
  (start_state : σ)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonNFA
  (α : Type)
  (σ : Type) :
  Type :=
  (symbol_arrow_list : List (SymbolArrow α σ))
  (epsilon_arrow_list : List (EpsilonArrow σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


def epsilon_arrow_list_to_graph
  {σ : Type} :
  List (EpsilonArrow σ) → Graph σ
  | [] => []
  | (hd :: tl) => (hd.start_state, hd.stop_state_list) :: epsilon_arrow_list_to_graph tl

/-
def epsilon_arrow_list_to_graph
  {σ : Type}
  (xs : List (EpsilonArrow σ)) :
  Graph σ :=
  xs.map (fun (x : EpsilonArrow σ) => (x.start_state, x.stop_state_list))
-/

def EpsilonNFA.epsilon_closure
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ) :
  List σ :=
  dft (epsilon_arrow_list_to_graph e.epsilon_arrow_list) state_list


/--
  The accumulated stop states of all of the arrows in the list that have a start state and symbol matching the given state and symbol.
-/
def symbol_arrow_list_to_fun
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (symbol_arrow_list : List (SymbolArrow α σ))
  (start_state : σ)
  (symbol : α) :
  List σ :=
  (symbol_arrow_list.filterMap (fun (arrow : SymbolArrow α σ) =>
    if arrow.start_state = start_state ∧ arrow.symbol = symbol
    then Option.some arrow.stop_state_list
    else Option.none)).join.dedup


example : symbol_arrow_list_to_fun ([] : List (SymbolArrow Char Nat)) 0 'a' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩] 0 'b' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'b' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'b' = [2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' = [1, 2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' = [1, 2] := by rfl


def EpsilonNFA.eval_one_no_eps
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (symbol : α) :
  List σ :=
  (starting_state_list.map (fun (state : σ) => (symbol_arrow_list_to_fun e.symbol_arrow_list) state symbol)).join.dedup


theorem EpsilonNFA.eval_one_no_eps_def
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (symbol : α)
  {stop_state : σ} :
  stop_state ∈ e.eval_one_no_eps starting_state_list symbol ↔
    (∃ (state : σ), state ∈ starting_state_list ∧ stop_state ∈ symbol_arrow_list_to_fun e.symbol_arrow_list state symbol) :=
  by
    simp only [eval_one_no_eps]
    simp


/--
  `EpsilonNFA.eval_one e xs c` := The list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `xs` and reads the symbol `c`.
-/
def EpsilonNFA.eval_one
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (symbol : α) :
  List σ :=
  e.epsilon_closure (starting_state_list.map (fun (state : σ) => (symbol_arrow_list_to_fun e.symbol_arrow_list) state symbol)).join.dedup


/--
  `EpsilonNFA.eval_from e xs cs` := The list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `xs` and reads the list of symbols `cs`.
-/
def EpsilonNFA.eval_from
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (input : List α) :
  List σ :=
  List.foldl e.eval_one (e.epsilon_closure starting_state_list) input


@[simp]
theorem EpsilonNFA.eval_from_on_nil
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ) :
  e.eval_from starting_state_list [] =
    e.epsilon_closure starting_state_list := rfl


@[simp]
theorem EpsilonNFA.eval_from_on_cons
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (c : α)
  (cs : List α) :
    e.eval_from starting_state_list (c :: cs) =
      e.eval_from (e.eval_one_no_eps (e.epsilon_closure starting_state_list) c) cs := rfl


/--
  `EpsilonNFA.eval e cs` := The list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `e.starting_state_list` and reads the list of symbols `cs`.
-/
def EpsilonNFA.eval
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  List σ :=
  e.eval_from e.starting_state_list input


/--
  `EpsilonNFA.accepts e cs` := True if and only if at least one of the states that the nondeterministic automaton `e` transitions to if it starts at the list of states `e.starting_state_list` and reads the list of symbols `cs` is an accepting state.
-/
def EpsilonNFA.accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ e.eval input ∧ s ∈ e.accepting_state_list


instance
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  Decidable (e.accepts input) :=
  by
  induction input
  all_goals
    simp only [EpsilonNFA.accepts]
    infer_instance



example : EpsilonNFA.eval_from ⟨ [⟨0, 'a', [1]⟩], [⟨0, [1]⟩], [0], [1] ⟩ [] ([] : List Char) = [] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [], [], [0], [1] ⟩ ([] : List Char) = [0] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [], [], [0], [1] ⟩ ['a'] = [] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩], [], [0], [1] ⟩ ['a'] = [1] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩], [], [0], [1] ⟩ ['b'] = [] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [], [0], [1] ⟩ ['a'] = [1] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [], [0], [1] ⟩ ['b'] = [1] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [], [0], [1] ⟩ ['a'] = [1] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [], [0], [1] ⟩ ['b'] = [2] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩], [], [0], [1] ⟩ ['a'] = [2, 1] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [], [⟨ 0, [1] ⟩], [0], [1] ⟩ ([] : List Char) = [1, 0] := by with_unfolding_all rfl

example : EpsilonNFA.eval ⟨ [], [⟨ 0, [1]⟩], [0], [1] ⟩ ['a'] = [] := by with_unfolding_all rfl


-------------------------------------------------------------------------------


structure AbstractEpsilonNFA
  (α : Type)
  (σ : Type) :
  Type :=
  (symbol : σ → α → σ → Prop)
  (epsilon : σ → σ → Prop)
  (start : σ → Prop)
  (accepting : σ → Prop)


def EpsilonNFA_symbol.toAbstract
  {α : Type}
  {σ : Type}
  (symbol_arrow_list : List (SymbolArrow α σ))
  :=
      fun (start_state : σ) (symbol : α) (stop_state : σ) =>
        ∃ (stop_state_list : List σ),
            ⟨start_state, symbol, stop_state_list⟩ ∈ symbol_arrow_list ∧
            stop_state ∈ stop_state_list


def EpsilonNFA.toAbstract
  {α : Type}
  {σ : Type}
  (e : EpsilonNFA α σ) :
  AbstractEpsilonNFA α σ :=
  {
    symbol :=
      fun (start_state : σ) (symbol : α) (stop_state : σ) =>
        ∃ (stop_state_list : List σ),
            ⟨start_state, symbol, stop_state_list⟩ ∈ e.symbol_arrow_list ∧
            stop_state ∈ stop_state_list,

    epsilon :=
      fun (start_state : σ) (stop_state : σ) =>
        ∃ (stop_state_list : List σ),
          ⟨start_state, stop_state_list⟩ ∈ e.epsilon_arrow_list ∧
          stop_state ∈ stop_state_list,

    start := fun (state : σ) => state ∈ e.starting_state_list,

    accepting := fun (state : σ) => state ∈ e.accepting_state_list
  }


/--
  `AbstractEpsilonNFA.eval e x cs` : True if and only if the state that the nondeterministic automaton `e` transitions to if it starts at the state `x` and reads the list of symbols `cs` is an accepting state.
-/
inductive AbstractEpsilonNFA.eval
  {α : Type}
  {σ : Type}
  (e : AbstractEpsilonNFA α σ) :
  σ → List α → Prop

  | eps
    (start_state : σ)
    (stop_state : σ)
    (input : List α) :
    -- Beginning from `stop_state` and evaluating `e` on `input` results in an accepting state.
    eval e stop_state input →

    -- There is an epsilon transition from `start_state` to `stop_state`.
    e.epsilon start_state stop_state →

    -- Beginning from `start_state` and evaluating `e` on `input` results in an accepting state.
    eval e start_state input

  | sym
    (start_state : σ)
    (c : α)
    (stop_state : σ)
    (cs : List α) :
    -- Beginning from `stop_state` and evaluating `e` on `cs` results in an accepting state.
    eval e stop_state cs →

    -- There is a symbol transition from `start_state` to `stop_state` on `c`.
    e.symbol start_state c stop_state →

    -- Beginning from `start_state` and evaluating `e` on `c :: cs` results in an accepting state.
    eval e start_state (c :: cs)

  | accept
    (start_state : σ) :
    -- `start_state` is an accepting state.
    e.accepting start_state →

    -- Beginning from `start_state` and evaluating `e` on an empty list of symbols results in an accepting state.
    eval e start_state []


def AbstractEpsilonNFA.accepts
  {α : Type}
  {σ : Type}
  (e : AbstractEpsilonNFA α σ)
  (input : List α) :
  Prop :=
  ∃ (start_state : σ), e.start start_state ∧ e.eval start_state input


theorem EpsilonNFA.eval_one_no_eps_iff
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (symbol : α)
  (stop_state : σ) :
  stop_state ∈ e.eval_one_no_eps starting_state_list symbol ↔
    (∃ (state : σ), state ∈ starting_state_list ∧ e.toAbstract.symbol state symbol stop_state) :=
  by
    simp only [EpsilonNFA.eval_one_no_eps]
    simp only [EpsilonNFA.toAbstract]
    simp only [symbol_arrow_list_to_fun]
    simp
    constructor
    · rintro ⟨_, h1, _, ⟨⟨⟩, h2, ⟨rfl, rfl⟩, rfl⟩, h3⟩
      exact ⟨_, h1, _, h2, h3⟩
    · rintro ⟨_, h1, _, h2, h3⟩
      exact ⟨_, h1, _, ⟨_, h2, ⟨rfl, rfl⟩, rfl⟩, h3⟩


abbrev AbstractEpsilonNFA.EpsilonClosure
  {α : Type}
  {σ : Type}
  (e : AbstractEpsilonNFA α σ) :
  σ → σ → Prop :=
  Relation.ReflTransGen e.epsilon


theorem EpsilonNFA.epsilon_closure_iff
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (state : σ) :
  state ∈ e.epsilon_closure starting_state_list ↔
    ∃ (start_state : σ), start_state ∈ starting_state_list ∧ e.toAbstract.EpsilonClosure start_state state :=
  by
    simp only [epsilon_closure]
    simp only [dft_iff]
    congr! with a b c
    simp [toAbstract]
    induction e.epsilon_arrow_list <;> simp [*, epsilon_arrow_list_to_graph, or_and_right, exists_or]
    apply or_congr_left <| exists_congr fun a => and_congr_left fun _ => ?_
    constructor <;> [rintro ⟨rfl, rfl⟩; rintro rfl] <;> [rfl; constructor <;> rfl]


theorem EpsilonNFA.eval_from_iff
  {α : Type}
  {σ : Type}
  [DecidableEq α]
  [DecidableEq σ]
  (M : EpsilonNFA α σ)
  (S : List σ)
  (input : List α) :
  (∃ s ∈ M.eval_from S input, s ∈ M.accepting_state_list) ↔
    (∃ s ∈ S, M.toAbstract.eval s input) :=
  by
    induction input generalizing S with simp
    | nil =>
      simp [epsilon_closure_iff]
      constructor
      · intro ⟨s, ⟨s', h1, h2⟩, h3⟩
        refine ⟨_, h1, ?_⟩
        clear h1
        induction h2 using Relation.ReflTransGen.head_induction_on with
        | refl => exact .accept _ h3
        | head h _ ih => exact .eps _ _ _ ih h
      · intro ⟨s, h1, h2⟩
        obtain ⟨s', h3, h4⟩ : ∃ s', M.toAbstract.EpsilonClosure s s' ∧ s' ∈ M.accepting_state_list := by
          clear h1; generalize e : [] = l at h2
          induction h2 with cases e
          | accept _ h' => exact ⟨_, .refl, h'⟩
          | eps _ _ _ _ h2 ih =>
            have ⟨s', h3, h4⟩ := ih rfl
            exact ⟨_, .head h2 h3, h4⟩
        exact ⟨_, ⟨_, h1, h3⟩, h4⟩
    | cons a as IH =>
      simp [IH, epsilon_closure_iff, eval_one_no_eps_iff]
      constructor
      · intro ⟨s₁, ⟨s₂, ⟨s₃, h1, h2⟩, h3⟩, h4⟩
        refine ⟨_, h1, ?_⟩
        clear h1
        induction h2 using Relation.ReflTransGen.head_induction_on with
        | refl => {apply AbstractEpsilonNFA.eval.sym _ _ _ _ h4 h3;  }
        | head h _ ih => exact .eps _ _ _ ih h
      · intro ⟨s, h1, h2⟩
        obtain ⟨s₁, s₂, h3, h4, h5⟩ :
            ∃ s₁ s₂, M.toAbstract.EpsilonClosure s s₂ ∧
              M.toAbstract.symbol s₂ a s₁ ∧ M.toAbstract.eval s₁ as := by
          clear h1; generalize e : a::as = l at h2
          induction h2 with cases e
          | sym _ _ _ _ h1 h2 => exact ⟨_, _, .refl, h2, h1⟩
          | eps _ _ _ h1 h2 ih =>
            have ⟨s₁, s₂, h3, h4, h5⟩ := ih rfl
            exact ⟨_, _, .head h2 h3, h4, h5⟩
        exact ⟨_, ⟨_, ⟨_, h1, h3⟩, h4⟩, h5⟩


theorem EpsilonNFA.accepts_iff
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input) :
  e.accepts input ↔ e.toAbstract.accepts input :=
  by
    simp [accepts, eval]
    rw [EpsilonNFA.eval_from_iff]
    rfl


-------------------------------------------------------------------------------


def EpsilonNFA.map
  {α : Type}
  {σ₁ σ₂ : Type}
  (f : σ₁ → σ₂)
  (e : EpsilonNFA α σ₁) :
  EpsilonNFA α σ₂ :=
  {
    symbol_arrow_list := e.symbol_arrow_list.map (fun (arrow : SymbolArrow α σ₁) => ⟨
      f arrow.start_state,
      arrow.symbol,
      arrow.stop_state_list.map f
    ⟩),
    epsilon_arrow_list := e.epsilon_arrow_list.map (fun (arrow : EpsilonArrow σ₁) => ⟨
      f arrow.start_state,
      arrow.stop_state_list.map f
    ⟩),
    starting_state_list := e.starting_state_list.map f,
    accepting_state_list := e.accepting_state_list.map f
  }


def AbstractEpsilonNFA.comap
  {α : Type}
  {σ₁ σ₂ : Type}
  (f_inv : σ₂ → σ₁)
  (e : AbstractEpsilonNFA α σ₁) :
  AbstractEpsilonNFA α σ₂ :=
  {
    symbol := fun (start_state : σ₂) (symbol : α) (stop_state: σ₂) =>
    (e.symbol (f_inv start_state) symbol (f_inv stop_state)),

    epsilon := fun (start_state : σ₂) (stop_state: σ₂) =>
    (e.epsilon (f_inv start_state) (f_inv stop_state)),

    start := fun (state : σ₂) => e.start (f_inv state),

    accepting := fun (state : σ₂) => e.accepting (f_inv state)
  }


def AbstractEpsilonNFA.map
  {α : Type}
  {σ₁ σ₂ : Type}
  (f : σ₁ → σ₂)
  (e : AbstractEpsilonNFA α σ₁) :
  AbstractEpsilonNFA α σ₂ :=
  {
    symbol :=
      fun (start_state : σ₂) (symbol : α) (stop_state: σ₂) =>
        ∃ (start_state' : σ₁) (stop_state': σ₁),
          f start_state' = start_state ∧
          f stop_state' = stop_state ∧
          e.symbol start_state' symbol stop_state',

    epsilon :=
      fun (start_state : σ₂) (stop_state: σ₂) =>
        ∃ (start_state' : σ₁) (stop_state': σ₁),
          f start_state' = start_state ∧
          f stop_state' = stop_state ∧
          e.epsilon start_state' stop_state',

    start :=
      fun (state : σ₂) =>
        ∃ (state' : σ₁), f state' = state ∧ e.start state',

    accepting :=
      fun (state : σ₂) =>
        ∃ (state' : σ₁), f state' = state ∧ e.accepting state'
  }
