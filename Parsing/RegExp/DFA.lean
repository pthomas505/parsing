import FOL.Parsing.NFA


set_option autoImplicit false


/--
  The type of deterministic automatons.
  `α` is the type of input characters.
  `σ` is the type of states.

  Transitions from one state to another state on each input character. The state that it transitions to is permitted to be the same state that it transitioned from.

  If the deterministic automaton `D` is at state `s` and the input sequence is `c :: cs` then `D` transitions to the state given by `D.step s c` and the input sequence becomes `cs`.
-/
structure DFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (step : σ → α → σ)
  (starting_state : σ)
  (accepting_state_list : List σ)


def DFA.eval_from
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (D : DFA α σ)
  (starting_state : σ) :
  List α → σ :=
  List.foldl D.step starting_state


/--
  `DFA.eval D cs` := Returns the final state that the deterministic automaton `D` transitions to if it starts at `D.startingState` and consumes the list of characters `cs`.
-/
def DFA.eval
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (D : DFA α σ) :
  List α → σ :=
  D.eval_from D.starting_state


def DFA.accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (D : DFA α σ)
  (input : List α) :
  Prop :=
  D.eval input ∈ D.accepting_state_list


/--
  The subset construction of a deterministic automaton from a nondeterministic automaton.

  Each state in the deterministic automaton is a subset of the states of the nondeterministic automaton.
-/
def NFA.to_DFA
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (N : NFA α σ) :
  DFA α (List σ) :=
  {
    step := N.eval_one
    starting_state := N.starting_state_list
    accepting_state_list := sorry
  }


example
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (N : NFA α σ) :
  (NFA.to_DFA N).starting_state = N.starting_state_list :=
  by rfl


lemma DFA.mem_accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (D : DFA α σ)
  (input : List α) :
  D.accepts input ↔
    D.eval_from D.starting_state input ∈ D.accepting_state_list := by rfl


/--
  The subset construction of a deterministic automaton from a nondeterministic automaton yields a deterministic automaton that is equivalent to the nondeterministic automaton.
-/
theorem NFA_to_DFA_is_equiv
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (N : NFA α σ) :
  N.to_DFA.accepts = N.accepts :=
  by
  ext cs
  simp only [DFA.mem_accepts]
  simp only [NFA.mem_accepts]
  simp only [NFA.to_DFA]
  sorry
/-
  simp
  constructor
  all_goals
    simp
    intro s a1 a2
    apply Exists.intro s
    tauto
-/
