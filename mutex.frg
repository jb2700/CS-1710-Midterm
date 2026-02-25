#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig State {}
one sig States {
  firstState: one State,
  next: pfunc State -> State
}

sig Thread {   
  ID: one Int,
  // this represents the index of the instruction that will be executed during a given timestamp.
  next_instr: func State -> Int,
  blocked: func State -> Boolean
}

pred SequentialExecution {
  all t: Thread | {
    t.next_instr[States.firstState] = 0 // everyone starts on the first instruction
    all s: State | {
      some States.next[s] implies {
        t.blocked[s] = True implies {
          t.next_instr[States.next[s]] = t.next_instr[s]
        } else {
          t.next_instr[States.next[s]] = add[t.next_instr[s], 1]
        }
      }
    }
  }
}

pred ThreadIDsUnique {
  // TODO
}

pred ValidFirstState {
  no prev : State | States.next[prev] = States.firstState
}

pred DeadlockFree[instr: Int] {
  // For all states, some thread makes progress...
  some t: Thread, s: State | {
    t.next_instr[s] = instr
  }
}

pred StarvationFree[instr: Int] {
  all t: Thread | {
    some s: State | {
      t.next_instr[s] = instr
    }
  } 
}

run {
  // ValidFirstState
  SequentialExecution
  // DeadlockFree[3]
  // StarvationFree[4]
  #Thread > 2
} for exactly 6 States for { next is linear }