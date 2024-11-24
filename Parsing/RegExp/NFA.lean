import FOL.Parsing.EpsilonNFA


set_option autoImplicit false


structure NFA
  (α : Type)
  (σ : Type) :
  Type :=
  (symbol_arrow_list : List (SymbolArrow α σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


/--
  `NFA.eval_one e l c` := Returns the list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `l` and consumes the symbol `c`.
-/
@[simp]
def NFA.eval_one
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (state_list : List σ)
  (symbol : α) :
  List σ :=
  (state_list.map (fun (state : σ) => (symbol_arrow_list_to_fun e.symbol_arrow_list) state symbol)).join.dedup



@[simp]
def NFA.eval_from
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (starting_state_list : List σ)
  (input : List α) :
  List σ :=
  List.foldl e.eval_one starting_state_list input


/--
  `NFA.eval e cs` := Returns the final list of states that the nondeterministic automaton `e` transitions to if it starts at `e.starting_state_list` and consumes the list of symbols `cs`.
-/
@[simp]
def NFA.eval
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (input : List α) :
  List σ :=
  e.eval_from e.starting_state_list input


example : NFA.eval ⟨ [], [0], [1] ⟩ ['a'] = [] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩], [0], [1] ⟩ ['a'] = [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩], [0], [1] ⟩ ['b'] = [] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [0], [1] ⟩ ['a'] = [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [0], [1] ⟩ ['b'] = [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [0], [1] ⟩ ['a'] = [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [0], [1] ⟩ ['b'] = [2] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩], [0], [1] ⟩ ['a'] = [1, 2] := by rfl


@[simp]
def NFA.accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ e.eval input ∧ s ∈ e.accepting_state_list


instance
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (input : List α) :
  Decidable (e.accepts input) :=
  by
  induction input
  all_goals
    simp only [NFA.accepts]
    infer_instance


lemma NFA.mem_accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (input : List α) :
  e.accepts input ↔
    ∃ (s : σ), s ∈ e.eval_from e.starting_state_list input ∧
      s ∈ e.accepting_state_list := by rfl
