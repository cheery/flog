# -*- encoding: utf-8 -*-
import core
import obj

# Pattern hole for constraint handling rule patterns.
class Hole(obj.Object):
    def __init__(self, key):
        self.key = key

    def to_str(self, rbp=0):
        return "$HOLE{" + str(self.key) + "}"

class Storage:
    def __init__(self, rules, subst, constraints, nextcid, notes, killed, hist):
        self.rules = rules
        self.subst = subst
        self.constraints = constraints
        self.nextcid = nextcid
        self.notes = notes
        self.killed = killed
        self.hist = hist

default_rules = [] # Filled later.

def empty(rules=default_rules):
    return Storage(
        rules = rules,
        subst = {},
        constraints = {},
        nextcid = 0,
        notes = {},
        killed = {},
        hist = {})

def copy_constraints(constraints):
    nconstraints = {}
    for sig, table in constraints.items():
        nconstraints[sig] = table.copy()
    return nconstraints

def copy_notes(notes):
    nnotes = {}
    for key, table in notes.items():
        nnotes[key] = table.copy()
    return nnotes

class ConstraintSignature(obj.Object):
    def __init__(self, name, arity):
        self.name = name
        self.arity = arity

    def rep(self):
        name = self.name.encode('utf-8')
        return "%s/%d" % (name, self.arity)

class Constraint(object):
    def __init__(self, sig, term, id):
        self.sig = sig
        self.term = term
        self.id = id

    def to_str(self):
        return self.term.to_str() + "#" + str(self.id)

class frozenlist(object):
    def __init__(self, list):
        self.list = list

    def __hash__(self):
        return hash(self.list)

    def __iter__(self):
        return iter(self.list)

# TODO: we need separate style for constraints.
def make_constraint(sig, args, state):
    if sig.arity != len(args):
        raise obj.RuntimeTypeError()
    term = obj.Data(0, args)
    c = Constraint(sig, walk(term, state.subst), state.nextcid)
    state = Storage(state.rules,
                    state.subst,
                    state.constraints,
                    state.nextcid+1,
                    state.notes,
                    state.killed,
                    state.hist)
    return reactivate(c, state)

def get_constraints(state):
    out = []
    for table in state.constraints.itervalues():
        for c in table.itervalues():
            out.append(obj.Data(0, [c.sig, c.term]))
    return out

def alive(c, state):
    if c.id in state.killed:
        return False
    return True
    # We won't access constraints outside our scope.
    #table = state.constraints.get(c.sig, None)
    #if table is not None:
    #    if c.id in table:
    #        return True
    #return False

def kill(c, state):
    state = Storage(state.rules,
                    state.subst,
                    state.constraints,
                    state.nextcid,
                    state.notes,
                    state.killed.copy(),
                    state.hist)
    state.killed[c.id] = c
    #import os
    #os.write(1, "kill %s\n" % c.to_str())
    return state

def suspend(c, state):
    killed = state.killed
    state = Storage(state.rules,
                    state.subst,
                    copy_constraints(state.constraints),
                    state.nextcid,
                    copy_notes(state.notes),
                    {},
                    state.hist)
    if c.id not in killed:
        add_notes(c.term, state, c)
        table = state.constraints.get(c.sig, None)
        if table is None:
            state.constraints[c.sig] = table = {}
        table[c.id] = c
    if len(killed) > 0: # Clean propagation history
        state.hist = state.hist.copy()
        for entry in state.hist.keys():
            remove = False
            for i in entry:
                remove |= (i in killed)
            if remove:
                state.hist.pop(entry, None)
    for k in killed.itervalues():
        table = state.constraints.get(k.sig, None)
        if table is not None:
            table.pop(c.id, None)
    return state

def add_notes(term, state, c):
    term = term.enter([])
    if isinstance(term, obj.Var):
        notes = state.notes
        wakeups = notes.get(term.key, None)
        if wakeups is None:
            notes[term.key] = wakeups = {}
        wakeups[c.id] = c
    elif isinstance(term, obj.Data):
        for arg in term.args:
            add_notes(arg, state, c)

class Walker(obj.Object): # Lazy version of a walk
    def __init__(self, term, subst):
        self.term = term
        self.subst = subst

    def enter(self, args):
        term = self.term.enter([])
        if isinstance(term, obj.Var):
            val = self.subst.get(term.key, None)
            if val is None:
                return term.enter(args)
            else:
                return Walker(val, self.subst).enter(args)
        elif isinstance(term, obj.Data):
            nargs = []
            for arg in term.args:
                nargs.append(Walker(arg, self.subst))
            return obj.Data(term.tag, nargs)
        else:
            return term.enter(args)

def walk(term, subst):
    term = term.enter([])
    if isinstance(term, obj.Var):
        val = subst.get(term.key, None)
        if val is None:
            return term
        else:
            return walk(val, subst)
    elif isinstance(term, obj.Data):
        nargs = []
        for arg in term.args:
            nargs.append(walk(arg, subst))
        return obj.Data(term.tag, nargs)
    else:
        return term

def extS(key, term, state):
    if occurs(key, term, state.subst):
        return None
    else:
        nnotes = state.notes
        nsubst = state.subst.copy()
        nsubst[key] = term
        if key in state.notes:
            nnotes = copy_notes(state.notes)
            wakeups = nnotes.pop(key)
        else:
            wakeups = {}
        state = Storage(state.rules,
                        nsubst,
                        state.constraints,
                        state.nextcid,
                        nnotes,
                        state.killed,
                        state.hist)
        states = [state]
        if len(wakeups) > 0:
            state.constraints = copy_constraints(state.constraints)
            # When waking up constraints, ideally we want to replicate
            # the situation when they were added the first time.
            for c in wakeups.values():
                state.constraints[c.sig].pop(c.id, None)
            for c in wakeups.values():
                nstates = []
                for state in states:
                    if not alive(c, state):
                        continue
                    sts = reactivate(Constraint(c.sig, walk(c.term, state.subst), c.id), state)
                    nstates.extend(sts)
                states = nstates
        return states

def fresh(state):
    ec = core.get_ec()
    v = obj.Var(ec.next_variable)
    ec.next_variable += 1
    nstate = Storage(state.rules,
                     state.subst,
                     state.constraints,
                     state.nextcid,
                     state.notes,
                     state.killed,
                     state.hist)
    return (v, nstate)

class Combinator(obj.Object):
    def go(self, state):
        assert False

class eq(Combinator):
    def __init__(self, t1, t2):
        self.t1 = t1
        self.t2 = t2

    def go(self, state):
        #t1s = walk(self.t1, state.subst).to_str()
        #t2s = walk(self.t2, state.subst).to_str()
        t1 = walk(self.t1, state.subst)
        t2 = walk(self.t2, state.subst)
        #import os
        #os.write(2, "¤ %s = %s\n" % (t1.rep(), t2.rep()))
        res = unify(t1, t2, state)
        if len(res) == 0:
            #import os
            #os.write(1, "fail at %s = %s\n" % (t1.rep(), t2.rep()))
            #for key, term in state.subst.items():
            #    os.write(1, "%d = %s\n" % (key, walk(term,state.subst).rep()))
            return []
        return res

def unify(t1, t2, state):
    #import os
    #os.write(1, t1.rep() + " == " + t2.rep() + "\n")
    if isinstance(t1, obj.Var) and isinstance(t2, obj.Var) and t1.key == t2.key:
        return [state]
    elif isinstance(t1, obj.Var):
        return extS(t1.key, t2, state)
    elif isinstance(t2, obj.Var):
        return extS(t2.key, t1, state)
    elif isinstance(t1, obj.Data) and isinstance(t2, obj.Data):
        if t1.tag == t2.tag and len(t1.args) == len(t2.args):
            states = [state]
            for i in range(0, len(t1.args)):
                nstates = []
                for state in states:
                    states = unify(t1.args[i], t2.args[i], state)
                    nstates.extend(states)
                states = nstates
            return states
        else:
            return []
    elif isinstance(t1, obj.String) and isinstance(t2, obj.String):
        if t1.string == t2.string:
            return [state]
    elif isinstance(t1, obj.Integer) and isinstance(t2, obj.Integer):
        if t1.number == t2.number:
            return [state]
    else:
        return []

def occurs(key, term, subst):
    term = term.enter([])
    if isinstance(term, obj.Var):
        val = subst.get(term.key, None)
        if val is not None:
            return occurs(key, val, subst)
        else:
            return term.key == key
    elif isinstance(term, obj.Data):
        for arg in term.args:
            if occurs(key, arg, subst):
                return True
        return False
    else:
        return False

class Unit(Combinator):
    def go(self, state):
        return [state]

class Fail(Combinator):
    def go(self, state):
        return []

tt = Unit()
ff = Fail()

class disj(Combinator):
    def __init__(self, g1, g2):
        assert isinstance(g1, Combinator)
        assert isinstance(g2, Combinator)
        self.g1 = g1
        self.g2 = g2

    def go(self, state):
        return self.g1.go(state) + self.g2.go(state)

class conj(Combinator):
    def __init__(self, g1, g2):
        assert isinstance(g1, Combinator)
        assert isinstance(g2, Combinator)
        self.g1 = g1
        self.g2 = g2

    def go(self, state):
        res = []
        for nstate in self.g1.go(state):
            res.extend(self.g2.go(nstate))
        return res

class constraint(Combinator):
    def __init__(self, sig, args):
        self.sig = sig
        self.args = args

    def go(self, state):
        return make_constraint(self.sig, self.args, state)

def match(term, pattern, table):
    term = term.enter([])
    #import os
    #os.write(2, "match %s = %s\n" % (term.rep(), pattern.rep()))
    if isinstance(term, obj.Var) and isinstance(pattern, obj.Var):
        if term.key == pattern.key:
            return table
    elif isinstance(pattern, Hole):
        other = table.get(pattern.key, None)
        if other is None:
            table = table.copy()
            table[pattern.key] = term
            return table
        else:
            return match(term, other, table)
    elif isinstance(term, obj.Data) and isinstance(pattern, obj.Data):
        if term.tag == pattern.tag and len(term.args) == len(pattern.args):
            for i in range(0, len(term.args)):
                table = match(term.args[i], pattern.args[i], table)
                if table is None:
                    return None
            return table
    elif isinstance(term, obj.String) and isinstance(pattern, obj.String):
        if term.string == pattern.string:
            return table
    elif isinstance(term, obj.Integer) and isinstance(pattern, obj.Integer):
        if term.number == pattern.number:
            return table
    #import os
    #os.write(2, "match %s = %s fail\n" % (term.rep(), pattern.rep()))
    return None

def lookup(sig, state):
    table = state.constraints.get(sig, None)
    if table is None:
        return {}.itervalues()
    return table.itervalues()

def reactivate(c, state):
    #import os
    #os.write(1, "reactivate %s\n" % c.to_str())
    goals = tt
    live = True
    i = 0
    for rule in state.rules:
        #os.write(1, "rule %d\n" % i)
        holes = rule.filter(c.sig)
        slots = rule.select()
        for index in holes:
            #os.write(1, "occ %d,%d\n" % (i, index))
            for table, row, kills in cartesian(slots, index, c, state):
                live = True
                for r in row.values():
                    live = live and alive(r, state)
                if not live:
                    continue
                if not len(row) == len(slots): # duplicates on row.
                    continue
                args = make_args(rule.arity, table)
                try:
                    if not obj.to_bool(rule.guard.enter(args)):
                        continue
                except obj.RuntimeTypeError:
                    continue
                for k in kills:
                    state = kill(k, state)
                if len(kills) == 0:
                    entry = frozenlist(row.keys() + [~i])
                    if entry in state.hist:
                        continue
                    hist = state.hist.copy()
                    hist[entry] = None
                    state = Storage(state.rules,
                                    state.subst,
                                    state.constraints,
                                    state.nextcid,
                                    state.notes,
                                    state.killed,
                                    hist)
                goals = conj(goals, Handler(rule.body, args))
                live = alive(c, state)
                if not live:
                    break
            if not live:
                break
        if not live:
            break
        i += 1
    state = suspend(c, state)
    return goals.go(state)

def make_args(arity, table):
    args = []
    for k in range(arity):
        args.append(table[k])
    args.reverse()
    return args

class Handler(Combinator):
    def __init__(self, body, args):
        self.body = body
        self.args = args

    def go(self, state):
        combi = self.body.enter(self.args)
        combi = combi.enter([])
        if isinstance(combi, Combinator):
            return combi.go(state)
        raise obj.RuntimeTypeError()

# Cartesian match across all slots.
def cartesian(slots, index, c, state):
    if len(slots) == 0:
        return [({}, {}, [])]
    out = []
    for table, row, kills in cartesian(slots[1:len(slots)], index-1, c, state):
        #print "table"
        #for key, item in table.iteritems():
        #    print "  " + str(key) + " = " + item.to_str()
        k, sig, pat = slots[0]
        if index == 0:
            tab = match(c.term, pat, table)
            if tab is None:
                continue
            r = row.copy()
            r[c.id] = c
            if k:
                out.append((tab, r, kills + [c]))
            else:
                out.append((tab, r, kills))
        else:
            for nc in lookup(sig, state):
                if not alive(nc, state):
                    continue
                tab = match(nc.term, pat, table)
                if tab is None:
                    continue
                r = row.copy()
                r[nc.id] = nc
                if k:
                    out.append((tab, r, kills + [c]))
                else:
                    out.append((tab, r, kills))
    return out

class Rule(object):
    def __init__(self, arity, keep, remove, guard, body):
        self.arity = arity
        self.keep = keep
        self.remove = remove
        self.guard = guard
        self.body = body

    def filter(self, sig):
        top = len(self.keep) + len(self.remove) - 1
        out = []
        while top >= 0:
            if len(self.keep) <= top:
                if sig == self.remove[top-len(self.keep)][0]:
                    out.append(top)
            elif top < len(self.keep):
                if sig == self.keep[top][0]:
                    out.append(top)
            top -= 1
        return out

    def select(self):
        out = []
        for sig, term in self.keep:
            out.append((False, sig, term))
        for sig, term in self.remove:
            out.append((True, sig, term))
        return out

class AlwaysTrue(obj.Object):
    def __init__(self):
        pass

    def enter(self, args):
        return obj.true
always_true = AlwaysTrue()

#codata River $a where
#    bind : River $a → ($a → River $b) → River $b
#    plus : River $a → River $a → River $a
#    step : River $a → Chain $a (River $a)
#
#data Chain $a $as where
#    empty : Chain $a $as
#    chain : $a → $as → Chain $a $as
#
#blank : River $a
#blank = cocase {
#    bind _ f  ⇒ blank ;
#    plus _ ys ⇒ ys ;
#    step _    ⇒ empty }
#
#another : $a → River $a → River $a
#another x xs = cocase {
#    bind _ f  ⇒ plus (f x) (bind xs f) ;
#    plus _ zs ⇒ another x (plus zs xs) ;
#    step _    ⇒ chain x xs }
#
#delayed : River $a → River $a
#delayed xs = cocase {
#    bind _ f  ⇒ delayed (bind xs f) ;
#    plus _ zs ⇒ delayed (plus zs xs) ;
#    step _    ⇒ step xs }

def River(bind, plus, step):
    return obj.Data(0, [bind, plus, step])

def bind(river, f):
    river = obj.to_data(river)
    return obj.call(river.args[0], river, f)

def plus(river, other):
    river = obj.to_data(river)
    return obj.call(river.args[1], river, other)

def step(river):
    river = obj.to_data(river)
    return obj.call(river.args[2], river)

class river_handler(obj.Object):
    def __init__(self, mode, env):
        self.mode = mode
        self.env = env

    def enter(self, args):
        mode = self.mode
        env = self.env
        if mode == 0: # blank
            return River(
                blank,
                river_handler(1, []),
                obj.Data(0, []))
        if mode == 1:
            ys = args[len(args) + ~1]
            return ys
        if mode == 2: # another
            x = args[len(args) + ~0]
            xs = args[len(args) + ~1]
            return River(
                river_handler(3, [x, xs]),
                river_handler(4, [x, xs]),
                obj.Data(1, [x, xs]))
        if mode == 3: # plus (f x) (bind xs f)
            x = env[0]
            xs = env[1]
            f = args[len(args) + ~1]
            return plus(call(f, x), bind(xs, f))
        if mode == 4: # another x (plus zs xs)
            x = env[0]
            xs = env[1]
            zs = args[len(args) + ~1]
            return call(another, x, plus(zs, xs))
        if mode == 5: # delayed
            xs = args[len(args) + ~0]
            return River(
                river_handler(6, [xs]),
                river_handler(7, [xs]),
                river_handler(8, [xs]))
        if mode == 6: # delayed (bind xs f)
            xs = env[0]
            f = args[len(args) + ~1]
            return call(delayed, bind(xs, f))
        if mode == 7: # delayed (plus zs xs)
            xs = env[0]
            zs = args[len(args) + ~1]
            return call(delayed, plus(zs, xs))
        if mode == 8: # step xs
            xs = env[0]
            return step(xs)

blank = river_handler(0, [])
another = river_handler(2, [])
delayed = river_handler(5, [])
