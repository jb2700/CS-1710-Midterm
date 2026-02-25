#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig State {}
sig Instr {}
one sig Main {
  firstState: one State,
  next: pfunc State -> State,
  firstInstr: one Instr,
  next_program_instr: pfunc Instr -> Instr
}

sig Thread {   
  ID: one Int,
  // this represents the index of the instruction that will be executed during a given timestamp.
  next_instr: func State -> Instr,
  blocked: func State -> Boolean
}

pred SequentialExecution {
  all t: Thread | {
    t.next_instr[Main.firstState] = Main.firstInstr // everyone starts on the first instruction
    all s: State | {
      some Main.next[s] implies {
        t.blocked[s] = True implies {
          t.next_instr[Main.next[s]] = t.next_instr[s]
        } else {
          t.next_instr[Main.next[s]] = Main.next_program_instr[t.next_instr[s]]
        }
      }
    }
  }
}

pred ThreadIDsUnique {
  // TODO
}

pred ValidFirstState {
  no prev : State | Main.next[prev] = Main.firstState
  no prev : Instr | Main.next_program_instr[prev] = Main.firstInstr
}

pred DeadlockFree {
  // For all instructions, some thread will eventually get there...
  all instr: Instr | {
    some t: Thread, s: State, s2: State | {
      t.next_instr[s] = instr
    }
  }
}

pred StarvationFree {
  all instr: Instr, t: Thread | {
    some s: State | {
      t.next_instr[s] = instr
    }
  } 
}

pred MutualExclusion[instr: Instr] {
  all disj t1: Thread, t2: Thread, s: State | {
    t1.next_instr[s] = instr implies {
      t2.next_instr[s] != instr
    }
  }
}

run {
  ValidFirstState
  SequentialExecution
  MutualExclusion[Main.next_program_instr[Main.firstInstr]]
  // DeadlockFree
  StarvationFree
  #Thread > 2
} for exactly 10 State, exactly 6 Instr for { 
  next is linear
  next_program_instr is linear 
}