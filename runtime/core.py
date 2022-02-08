from rpython.rlib.rthread import ThreadLocalReference
from continuations import Continuation

class ExecutionContext:
    def __init__(self, config):
        self.config = config
        self.sthread = None
        self.next_variable = 0

        #self.spawn_pool = []
        #self.running = []
        #self.scheduler = None # Start in scheduler.

class GlobalState:
    ec = ThreadLocalReference(ExecutionContext, loop_invariant=True)

g = GlobalState()

def init_executioncontext(*args):
    ec = ExecutionContext(*args)
    g.ec.set(ec)

def get_ec():
    ec = g.ec.get()
    if isinstance(ec, ExecutionContext):
        return ec
    import os
    os.write(2, "Threads don't support get_ec now.\n")
    assert False, "failure"
