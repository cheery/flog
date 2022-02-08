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
        #import os
        #t1s = walk(self.t1, state.subst).to_str()
        #t2s = walk(self.t2, state.subst).to_str()
        #os.write(2, "%s = %s\n" % (t1s, t2s))
        t1 = walk(self.t1, state.subst)
        t2 = walk(self.t2, state.subst)
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

#def dual(x, y):
#    return Term("dual", [x, y])

class AlwaysTrue(obj.Object):
    def __init__(self):
        pass

    def enter(self, args):
        return obj.true
always_true = AlwaysTrue()

# The CHR rule handler returns 'nothing' when guard doesn't pass.
#def chr_rule(keep, remove, guard=always_true):
#    def __decorator__(fn):
#        default_rules.append(Rule(keep, remove, guard, fn))
#        return fn
#    return __decorator__

#X = Hole(0)
#Y = Hole(1)
#Z = Hole(2)

#@chr_rule([], [dual(X, X)])
#def rule_0(bindings, state):
#    return ff.go(state)
#
#@chr_rule([dual(X, Y)], [dual(Y, Z)])
#def rule_1(bindings, state):
#    X = bindings[0]
#    Y = bindings[1]
#    Z = bindings[2]
#    return eq(X, Z).go(state)
#
#@chr_rule([dual(X, Y)], [dual(Z, Y)])
#def rule_2(bindings, state):
#    X = bindings[0]
#    Y = bindings[1]
#    Z = bindings[2]
#    return eq(X, Z).go(state)
#
#@chr_rule([dual(X, Y)], [dual(X, Z)])
#def rule_3(bindings, state):
#    X = bindings[0]
#    Y = bindings[1]
#    Z = bindings[2]
#    return eq(Y, Z).go(state)
#
#@chr_rule([dual(X, Y)], [dual(Z, X)])
#def rule_4(bindings, state):
#    X = bindings[0]
#    Y = bindings[1]
#    Z = bindings[2]
#    return eq(Y, Z).go(state)

#def atom(name):
#    return Term(name, [])
#
#def ap(x, y):
#    return Term("ap", [x, y])
#
#def tensor(x, y):
#    return ap(ap(Term("⊗", []), x), y)
#
#def par(x, y):
#    return ap(ap(Term("⅋", []), x), y)
#
#def plus(x, y):
#    return ap(ap(Term("+", []), x), y)
#
#def band(x, y):
#    return ap(ap(Term("&", []), x), y)
#
#def ofc(x):
#    return ap(Term("!", []), x)
#
#def que(x):
#    return ap(Term("?", []), x)
#
#unit = Term("1", [])
#zero = Term("0", [])
#top = Term("⊤", [])
#bot = Term("⊥", [])
#
#X = Hole(0)
#Y = Hole(1)
#Z = Hole(2)
#
#@chr_rule([], [dual(tensor(X,Y),Z)])
#@chr_rule([], [dual(Z,tensor(X,Y))])
#def rule_5(bindings, state):
#    C, state = fresh(state)
#    D, state = fresh(state)
#    X,Y,Z = bindings[0],bindings[1],bindings[2]
#    return conj(
#        eq(Z, par(C,D)),
#        conj(
#            constraint(dual(X,C)),
#            constraint(dual(Y,D)))).go(state)
#
#@chr_rule([], [dual(Z, par(X,Y))])
#@chr_rule([], [dual(par(X,Y), Z)])
#def rule_6(bindings, state):
#    C, state = fresh(state)
#    D, state = fresh(state)
#    X,Y,Z = bindings[0],bindings[1],bindings[2]
#    return conj(
#        eq(Z,tensor(C,D)),
#        conj(
#            constraint(dual(X,C)),
#            constraint(dual(Y,D)))).go(state)
#
#@chr_rule([], [dual(Z, plus(X,Y))])
#@chr_rule([], [dual(plus(X,Y), Z)])
#def rule_7(bindings, state):
#    C, state = fresh(state)
#    D, state = fresh(state)
#    X,Y,Z = bindings[0],bindings[1],bindings[2]
#    return conj(
#        eq(Z,band(C,D)),
#        conj(
#            constraint(dual(X,C)),
#            constraint(dual(Y,D)))).go(state)
#
#@chr_rule([], [dual(Z, band(X,Y))])
#@chr_rule([], [dual(band(X,Y), Z)])
#def rule_8(bindings, state):
#    C, state = fresh(state)
#    D, state = fresh(state)
#    X,Y,Z = bindings[0],bindings[1],bindings[2]
#    return conj(
#        eq(Z,plus(C,D)),
#        conj(
#            constraint(dual(X,C)),
#            constraint(dual(Y,D)))).go(state)
#
#@chr_rule([], [dual(Y, ofc(X))])
#@chr_rule([], [dual(ofc(X), Y)])
#def rule_9(bindings, state):
#    C, state = fresh(state)
#    X,Y = bindings[0],bindings[1]
#    return conj(
#        eq(Y,que(C)),
#            constraint(dual(X,C))).go(state)
#
#@chr_rule([], [dual(Y, que(X))])
#@chr_rule([], [dual(que(X), Y)])
#def rule_10(bindings, state):
#    C, state = fresh(state)
#    X,Y = bindings[0],bindings[1]
#    return conj(
#        eq(Y,ofc(C)),
#            constraint(dual(X,C))).go(state)
#
#@chr_rule([], [dual(X, unit)])
#@chr_rule([], [dual(unit, X)])
#def rule_11(bindings, state):
#    X = bindings[0]
#    return eq(X,bot).go(state)
#
#@chr_rule([], [dual(X, bot)])
#@chr_rule([], [dual(bot, X)])
#def rule_12(bindings, state):
#    X = bindings[0]
#    return eq(X,unit).go(state)
#
#@chr_rule([], [dual(X, zero)])
#@chr_rule([], [dual(zero, X)])
#def rule_13(bindings, state):
#    X = bindings[0]
#    return eq(X,top).go(state)
#
#@chr_rule([], [dual(X, top)])
#@chr_rule([], [dual(top, X)])
#def rule_13(bindings, state):
#    X = bindings[0]
#    return eq(X,zero).go(state)
#
#def demonstration():
#    state = empty()
#    x, state = fresh(state)
#    y, state = fresh(state)
#    z, state = fresh(state)
#    w, state = fresh(state)
#    h, state = fresh(state)
#    goal = conj(constraint(Term("dual", [x, y])),
#                constraint(Term("dual", [tensor(unit,par(x, y)), h])))
#
#    import os
#    os.write(1, "results for\n")
#    for state in goal.go(state):
#        os.write(1, "result:\n")
#        for var in state.subst:
#            os.write(1, "  %d = %s\n" % (var, walk(state.subst[var], state.subst).to_str()))
#        for cs in state.constraints.itervalues():
#            for c in cs.itervalues():
#                if alive(c, state):
#                    os.write(1, "  %s\n" % c.term.to_str())
#
#if __name__=="__main__":
#    demonstration()
