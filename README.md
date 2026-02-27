# CS-1710-Midterm

1. We are trying to model mutexes. What we are trying to prove is that using a lock enforces mutual exclusion (only ont thread can access a program instruction at a time). The way we do this is my spawning in a couple of threads. These threads all start on the same base instruction and we track them as they move through their instructions. We verify that even when threads run in a random order, two threads never hold the same lock or enter the same citical section simultaniously. 

2. In our model, we have two run statements (to run the model just run the mutex.frg file and to run the tests run the mutex.test.frg file). The first run statment is the mutual exclusion run statement and the second run statement is the locking run statement. When running the mutual exclusion model, go to table and then you can see the table and then look at the blocked + next_instr tables. In the next_instr table, we can see on the left the thread, the middle the state of the model, and the instruction the thread is on. In the beginning, all of the threads start at Instr0. So in this table you should be able to see that none of the threads are executing the same critical instruction which is the one passed in as a parameter to the MutualExclusion predicate (except for Instr0 where all threads are on that instruction but all threads but one should be blocked). In the blocked table you can see which thread is blocked or not, if it is true it is blocked and false means unblocked. For the second run statement, we are looking for a critical run section using a lock. So, if we look at the lock_instr we can see where the lock starts (for example at Instr_2) and in the unlock_instr we can see where the lock ends (for example at Instr_3). The instruction between these two is considered the critical section (in our example Instr_3). So, if we look at the next_instr table, we should never have two threads which are on the same critical section at the same state (for our example no threads are at Instr_3 at the same state). We have a check statement that proves our initial model where a lock enforces mutual exclusion. We do this by saying for all instructions that are not the initial instruction and there is a lock at that instruction, we should also have mutual exclusion for all threads at that particular instruction. 

3. We have 7 sigs in total. Two sigs are booleans which are used to represent the True/False states (for example is a thread is blocked we set the blocked field to true and if it is not we set it to false). Now we have a state and an instruction sig. The state sig is basically out time step so at time step t or at state s, here is a view of the threads/locks. The instruction sig just represents one line of instruction execution. Now we have our Main sig which is the overarching design of the model. It contains the first state and instruction as well as the next state and instructions. Now we have a thread sig, which has a unique ID, a next instruction func which maps the current state to the instruction to be executed, and a blocked func which takes in a state and returns a boolean whether or not the thread is blocked. Finally, we have a lock sig. This lock sig has a lock_instr which is an instruciton, an unlock_instr which is also an instruction, and a holder which maps a state to a thread. The idea is that if a thread holds the lock then they are able to access that unlock_instr and if the thread does not they must wait at the lock_instr. 

Predicates:

SequentialExecution: It says that if a thread is not blocked, it moves to the next instruction in the program. If it is blocked, it stays exactly where it is.

ValidFirstState: It ensures that the model begins at the very first state and the first instruction.

DeadlockFree / StarvationFree: Ensures that all threads eventually execute all instructions and do not get stuck forever.

MutualExclusion[instr]: It checks every single state and ensures that no two different threads are ever at the same instruction (the instr passed in) at the same time.

ValidLockInstrs: It makes sure every lock has a unique "Lock" instruction and a unique "Unlock" instruction, and that the Unlock instruction always comes after the Lock instruction in the program code. 

GettingLock: It says that if a thread hits a lock instruction, it can only continue if it successfully takes ownership of the lock. If someone else has it, the thread is marked as blocked.

HoldingLock: It ensures the lock holder keeps ownership until they reach the unlock instruction. Once they hit that, they must give it up so others can use it.

Wellformed: This is just the previous predicates all in one predicate so that I do not have to call each of the other ones individually. 


4. Our testing can be divided into tests for our individual predicates, and tests that aimed to prove something interesting about our domain area.

In terms of proofs about our domain area, `lock_around_instr_implies_mutex` proves that, in our model, having a lock around an instruction means that there will always be mutual exclusion on that instruction between threads.
`mutex_still_deadlock_free` proves that, in our model, no matter how many locks you have nor their configuration, the program will still be deadlock free (as long as threads always try to progress and locks will always let in a waiting thread if empty). 
This only really works because of the simplifications of our model (namely that critical sections must only be one instruction), but within this model programs must be deadlock free.
`mutex_still_starvation_free` does a similar thing for starvation freedom. 
An interesting note is that, here, we must restrict the number of `Instr`s and `Thread`s to be within a reasonable range of the number of `State`s so that there's sufficient time for the threads to all get through the program.

Our basic tests do a variety of things, mostly just double checking properties of our predicates and ensuring that common sense identities hold.
One interesting example is `starvation_free_implies_deadlock_free` which ensures that starvation freedom is validly a subset of deadlock freedom!

5. We documented our mutex and test file well. 