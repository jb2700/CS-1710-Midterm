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

pred DeadlockFree {
  // For all instructions, some thread will eventually get there...
  all instr: Instr | {
    some t: Thread, s: State, s2: State | {
      t.next_instr[s] = instr
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

pred MutualExclusion[instr: Instr] {
  all disj t1: Thread, t2: Thread, s: State | {
    t1.next_instr[s] = instr implies {
      t2.next_instr[s] != instr
    }
  }
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

  // TODO: make sure unlock is after lock
  all l: Lock | {
     Main.next_program_instr[Main.next_program_instr[l.lock_instr]] = l.unlock_instr
  }
}

// TODO: add a holding lock condition that the lock is held throughout critical section
// only one thread gets the lock, and only if it's unlocked
pred GettingLock {
  all l: Lock, t: Thread, s: State | {
    // if this thread is on my lock instruction...
    t.next_instr[s] = l.lock_instr implies {
        // if i'm not the holder of the mutex in the next step, I must block
        l.holder[Main.next[s]] != t iff t.blocked[s] = True
    }
  }
}

// TODO: check this
pred HoldingLock {
  all l: Lock, t: Thread, s: State | {
    // if i currently hold the lock
    l.holder[s] = t implies {
      // i only won't hold it in the next state if I am on the unlock instruction next
      l.holder[Main.next[s]] != t iff t.next_instr[Main.next[s]] = l.unlock_instr
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
  // DeadlockFree
  StarvationFree
  #Thread > 2
  #Lock > 0
} for exactly 10 State, exactly 6 Instr for { 
  next is linear
  next_program_instr is linear 
}

test suite for Wellformed {
  test expect {
    lock_around_instr_implies_mutex: {
      Wellformed implies {
        all i: Instr | {
          {
            // if we're not the first instruction
            i != Main.firstInstr
            // and there's some lock protecting this instruction
            some l: Lock | {
              Main.next_program_instr[l.lock_instr] = i
              l.unlock_instr = Main.next_program_instr[i]
            }
          } implies {
            // we should have mutual exclusion
            MutualExclusion[i]
          }
        }
      }
    } for {
      next is linear
      next_program_instr is linear 
    } is checked
  }
}

// test suite for Wellformed {
//   test expect {
//     mutex_still_deadlock_free: {
//       Wellformed implies {
//         DeadlockFree
//       }
//     } for 100 State, 10 Instr for {
//       next is linear
//       next_program_instr is linear 
//     } is checked
//   }
// }