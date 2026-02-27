#lang forge/froglet

open "mutex.frg"

// INTERESTING PROPERTY TESTS

// Safety Properties
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

// Liveness Properties
test expect {
  mutex_still_deadlock_free: {
    {
      Wellformed 
      ThreadsTryToGoWhenTheyCan 
      LocksMustLetSomeoneWaitingIn
    } implies {
      DeadlockFree
    }
  } for {
    next is linear
    next_program_instr is linear 
  } is checked

  // Note: this test can take a while (~30 sec on my machine), be patient
  mutex_still_starvation_free: {
    {
      Wellformed 
      ThreadsTryToGoWhenTheyCan 
      LocksMustLetSomeoneWaitingIn
    } implies {
      StarvationFree
    }
    // Need to constrain the number of instrs * threads vs number of states
    // (for the "given enough time" part of starvation freedom)
  } for exactly 100 State, 10 Instr, 5 Thread for {
    next is linear
    next_program_instr is linear 
  } is checked
}

// BASIC TESTS

test expect {
  can_execute_sequentially: {
    SequentialExecution
    ValidFirstState
  } is sat

  first_state_is_root: {
    ValidFirstState
    some prev: State | Main.next[prev] = Main.firstState
  } is unsat
}

test expect {
  can_be_deadlock_free: {
    DeadlockFree
    some Thread
    some Instr
  } is sat

  can_overlap_without_mutex: {
    some t1, t2: Thread, s: State, i: Instr | {
      t1 != t2
      t1.next_instr[s] = i
      t2.next_instr[s] = i
    }
  } is sat
}

test expect {
  lock_can_be_held: {
    some l: Lock, s: State, t: Thread | l.holder[s] = t
  } is sat

  locks_must_be_distinct: {
    ValidLockInstrs
    some disj l1, l2: Lock | l1.lock_instr = l2.lock_instr
  } is unsat

  must_block_if_not_granted: {
    GettingLock
    some l: Lock, t: Thread, s: State | {
      t.next_instr[s] = l.lock_instr
      l.holder[Main.next[s]] != t
      t.blocked[s] = False
    }
  } is unsat
  
  holding_logic_strict: {
    HoldingLock
    some l: Lock, t: Thread, s: State | {
      l.holder[s] = t
      l.holder[Main.next[s]] != t
      t.next_instr[Main.next[s]] != l.unlock_instr
    }
  } is unsat
}