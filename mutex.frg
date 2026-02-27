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

pred ValidFirstState {
  no prev : State | Main.next[prev] = Main.firstState
  no prev : Instr | Main.next_program_instr[prev] = Main.firstInstr
}

sig Lock {
  lock_instr: one Instr,
  unlock_instr: one Instr,
  holder: pfunc State -> Thread // the holder of this mutex on a given step
}

pred ValidLockInstrs {
  // They must be unique
  all disj l1: Lock, l2: Lock | {
    l1.lock_instr != l2.lock_instr
    l1.unlock_instr != l2.unlock_instr
  }

  all l: Lock | {
    // For now, they have to be exactly two instrs apart (critical section of length 1)
    Main.next_program_instr[Main.next_program_instr[l.lock_instr]] = l.unlock_instr
    not {some other: Lock | other.lock_instr = Main.next_program_instr[l.lock_instr]}
  }
}

// only one thread gets the lock, and only if it's unlocked
pred GettingLock {
  all l: Lock, t: Thread, s: State | {
    // if this thread is on my lock instruction...
    t.next_instr[s] = l.lock_instr implies {
        // if i'm not the holder of the mutex in the next step, I must block
        l.holder[Main.next[s]] != t implies t.blocked[s] = True
    }
  }
}

pred HoldingLock {
  all l: Lock, t: Thread, s: State | {
    // if i currently hold the lock
    l.holder[s] = t implies {
      // i only won't hold it in the next state if I am on the unlock instruction next
      l.holder[Main.next[s]] != t iff t.next_instr[Main.next[s]] = l.unlock_instr
    }
  }
}

pred LocksMustLetSomeoneWaitingIn {
  all l: Lock, s: State | {
    {
      some Main.next[s] implies {
        {
          some t: Thread | { t.next_instr[s] = l.lock_instr }
        } implies {
          some new: Thread | {
            new.next_instr[Main.next[s]] = Main.next_program_instr[l.lock_instr]
          }
        }
      }
    }
  }
}

pred ThreadsTryToGoWhenTheyCan {
  all t: Thread, s: State | {
    {
      not {
        some l: Lock | {
          t.next_instr[s] = l.lock_instr and l.holder[s] != t
        }
      }
    } implies {
      t.blocked[s] = False
    }
  }
}

pred Wellformed {
  ValidFirstState
  SequentialExecution
  GettingLock
  ValidLockInstrs
  HoldingLock
}


// **** INTERESTING PROPERTIES (we will prove) ****

// Liveness Properties

pred DeadlockFree {
  // For all instructions, some thread will eventually get there...
  all instr: Instr | {
    #Thread > 0 implies {
      some t: Thread, s: State, s2: State | {
        t.next_instr[s] = instr
      }
    }
  }
}

pred StarvationFree {
  // For all instructions, all threads will eventually get there...
  all instr: Instr, t: Thread | {
    some s: State | {
      t.next_instr[s] = instr
    }
  } 
}

test suite for DeadlockFree {
  test expect {
    starvation_free_implies_deadlock_free: {
      Wellformed implies {
        StarvationFree implies DeadlockFree
      }
    } for {
      next is linear
      next_program_instr is linear 
    } is checked
  }
}


// Liveness Properties

pred MutualExclusion[instr: Instr] {
  all disj t1: Thread, t2: Thread, s: State | {
    t1.next_instr[s] = instr implies {
      t2.next_instr[s] != instr
    }
  }
}

// **** RUN BLOCKS ****

run {
  Wellformed
  MutualExclusion[Main.next_program_instr[Main.firstInstr]] // enforce mutual exclusion on instr1
  // DeadlockFree
  StarvationFree
  #Thread > 2
} for exactly 10 State, exactly 6 Instr for { 
  next is linear
  next_program_instr is linear 
}

// if its wellformed and theres a lock on instr1 that always ensures mutual exclusion on instr1
run {
  Wellformed
  MutualExclusion[Main.next_program_instr[Main.firstInstr]] // enforce mutual exclusion on instr1
  StarvationFree
  #Thread > 2
  #Lock > 0
} for exactly 10 State, exactly 6 Instr for { 
  next is linear
  next_program_instr is linear 
}