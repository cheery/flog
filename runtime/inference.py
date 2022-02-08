# -*- encoding: utf-8 -*-
from ukanren import *
import obj
import transform
from parser import Nil, Cons

#constraint_check = ConstraintSignature(u"constraint_check", 4)
#constraint_hole = ConstraintSignature(u"constraint_hole", 3)

#constraint_check, [Cons(A,B), X, Y, Z] <=> 
#    Y = transform.App NY Q
#    constraint_hole A Q Z
#    constraint_check B X NY Z
#constraint_check, [Nil, X, Y, Z] <=> true | X=Y

class InferCode(Combinator):
    def __init__(self, types, env, term, constraints, restype, invocations, enums):
        self.types = types
        self.env = env
        self.term = term
        self.constraints = constraints
        self.restype = restype
        self.invocations = invocations
        self.enums = enums

    def go(self, state):
        term = obj.to_data(self.term)
        #import os
        #os.write(2, "typechecking %s\n" % term.rep())
        if term.tag == 0: #Var  = lambda index:        obj.Data(0, [obj.from_integer(index)])
            index = obj.to_integer(term.args[0])
            goal = conj(
                eq(self.restype, self.env[index]),
                eq(self.constraints, Nil))
                #tt) #eq(self.rterm, transform.Var(index)))
        elif term.tag == 1: #App  = lambda fn, arg:      obj.Data(1, [fn, arg])
            a, state = fresh(state)
            c1, state = fresh(state)
            c2, state = fresh(state)
            goal = conj(
                conj(
                    InferCode(self.types, self.env,
                        term.args[0], c1, arrow(a, self.restype), self.invocations, self.enums),
                    InferCode(self.types, self.env,
                        term.args[1], c2, a, self.invocations, self.enums)),
                append(c1, c2, self.constraints))
                #tt)#eq(self.rterm, transform.App(fn, arg)))
        elif term.tag == 2: #Abs  = lambda body:         obj.Data(2, [body])
            a, state = fresh(state)
            b, state = fresh(state)
            goal = conj(
                eq(self.restype, arrow(a, b)),
                conj(
                    InferCode(self.types, [a] + self.env,
                        term.args[0], self.constraints, b, self.invocations, self.enums),
                    tt #eq(self.rterm, transform.Abs(body))
                    ))
        elif term.tag == 3: #Let  = lambda bind, body:   obj.Data(3, [bind, body])
            a, state = fresh(state)
            c1, state = fresh(state)
            c2, state = fresh(state)
            goal = conj(
                conj(
                    InferCode(self.types, self.env,
                        term.args[0], c1, a, self.invocations, self.enums),
                    InferCode(self.types, [a] + self.env,
                        term.args[1], c2, self.restype, self.invocations, self.enums)),
                append(c1, c2, self.constraints))
                #tt) #eq(self.rterm, transform.Let(bind, body)))
        elif term.tag == 4: #Invoke = lambda name:       obj.Data(4, [name])
            name = obj.to_string(term.args[0])
            tr = obj.to_data(self.types[name])
            table = {}
            t, state = instantiate(tr.args[1], table, state)
            constraints, state = instantiate_constraints(tr.args[0], table, state)
            self.invocations[term] = t
            #t.args[0] constraint list
            #rt = t.args[1] # return type
            #envc = obj.from_integer(len(self.env)) # Where in environment the constraint checkpoint is.
            goal = conj(
                eq(self.restype, t),
                eq(self.constraints, obj.from_list(constraints)))
                #constraint(constraint_check, [t.args[0], term, self.rterm, envc]))
                #eq(self.rterm, transform.Invoke(obj.from_string(name))))
        elif term.tag == 5: #Const = lambda const:       obj.Data(5, [const])
            const = term.args[0].enter([])
            if isinstance(const, obj.Integer):
                goal = eq(self.restype, transform.TName(obj.from_string(u"Integer")))
            elif isinstance(const, obj.String):
                goal = eq(self.restype, transform.TName(obj.from_string(u"String")))
            else:
                raise obj.RuntimeTypeError()
            goal = conj(goal, eq(self.constraints, Nil))
            #goal = conj(goal, eq(self.rterm, transform.Const(const)))
        elif term.tag == 6: #Case = lambda bind,cases:   obj.Data(6, [bind,cases])
            a, state = fresh(state)
            c1, state = fresh(state)
            goal = InferCode(self.types, self.env,
                    term.args[0], c1, a, self.invocations, self.enums)
            for case in obj.to_list(term.args[1]):
                table = {}
                case = obj.to_data(case)
                enum = obj.to_string(case.args[0])
                if enum not in self.enums:
                    raise obj.RuntimeTypeError()
                datatype = self.enums[enum].datatype
                if datatype.co:
                    raise obj.RuntimeTypeError()
                index = self.enums[enum].index
                arity = obj.to_integer(case.args[1])
                arglist = datatype.cases[index][1]
                retty, state = instantiate(datatype.cases[index][2], table, state)
                goal = conj(goal, eq(retty, a))
                if arity != len(arglist):
                    raise obj.RuntimeTypeError()
                env = self.env
                args = []
                for i in range(arity):
                    k, state = instantiate(arglist[len(arglist) + ~i], table, state)
                    args.append(k)
                cenv = args + env
                cn, state = fresh(state)
                goal = conj(goal,
                    InferCode(self.types, cenv,
                    case.args[2], cn, self.restype, self.invocations, self.enums))
                cz, state = fresh(state)
                goal = conj(goal, append(c1, cn, cz))
                c1 = cz
            goal = conj(goal, eq(c1, self.constraints))
        elif term.tag == 7: #Cocase = lambda cases:      obj.Data(7, [cases])
            c1 = obj.from_list([])
            goal = tt
            for case in obj.to_list(term.args[0]):
                table = {}
                case = obj.to_data(case)
                enum = obj.to_string(case.args[0])
                if enum not in self.enums:
                    raise obj.RuntimeTypeError()
                datatype = self.enums[enum].datatype
                if not datatype.co:
                    raise obj.RuntimeTypeError()
                index = self.enums[enum].index
                arity = obj.to_integer(case.args[1])
                arglist = datatype.cases[index][1]
                retty, state = instantiate(datatype.cases[index][2], table, state)
                if arity != len(arglist):
                    raise obj.RuntimeTypeError()
                env = self.env
                args = []
                for i in range(arity):
                    k, state = instantiate(arglist[len(arglist) + ~i], table, state)
                    args.append(k)
                cenv = args + env
                goal = conj(goal, eq(args[len(args)-1], self.restype))
                cn, state = fresh(state)
                goal = conj(goal,
                    InferCode(self.types, cenv,
                        case.args[2], cn, retty, self.invocations, self.enums))
                cz, state = fresh(state)
                goal = conj(goal, append(c1, cn, cz))
                c1 = cz
            goal = conj(goal, eq(c1, self.constraints))
        elif term.tag == 8: #ScopeWalk = lambda term:    obj.Data(8, [term])
            goal = InferCode(self.types, self.env,
                term.args[0], self.constraints, self.restype, self.invocations, self.enums)
        else:
            raise obj.RuntimeTypeError()
        return goal.go(state)

def arrow(a, b):
    return transform.TApp(
        transform.TApp(transform.TName(obj.from_string(u"→")), a), b)

def generalize(type, table):
    type = type.enter([])
    if isinstance(type, obj.Var):
        res = table.get(type.key, None)
        if res is None:
            res = transform.TVar(len(table))
            table[type.key] = res
        return res
    type = obj.to_data(type)
    if type.tag == 0: #TVar  = lambda index:        obj.Data(0, [obj.from_integer(index)])
        index = obj.to_integer(type.args[0])
        res = table.get(~index, None)
        if res is None:
            res = transform.TVar(len(table))
            table[~index] = res
        return res
    elif type.tag == 1: #TApp  = lambda fn, arg:      obj.Data(1, [fn, arg])
        a = generalize(type.args[0], table)
        b = generalize(type.args[1], table)
        return transform.TApp(a, b)
    elif type.tag == 2: #TName = lambda name:         obj.Data(2, [name])
        return type
    else:
        raise obj.RuntimeTypeError()

def generalize_constraints(inp, table):
    constraints = []
    for c in inp:
        c = obj.to_data(c)
        con = c.args[0]
        datum = obj.to_data(c.args[1])
        nargs = []
        for arg in datum.args:
            arg = generalize(arg, table)
            nargs.append(arg)
        constraints.append(obj.Data(0, [con, obj.Data(0, nargs)]))
    return obj.from_list(constraints)

def instantiate(type, table, state):
    if isinstance(type, obj.Var):
        return type, state
    type = obj.to_data(type)
    if type.tag == 0: #TVar  = lambda index:        obj.Data(0, [obj.from_integer(index)])
        index = obj.to_integer(type.args[0])
        v = table.get(index, None)
        if v is None:
            v, state = fresh(state)
            table[index] = v
        return v, state
    elif type.tag == 1: #TApp  = lambda fn, arg:      obj.Data(1, [fn, arg])
        a, state = instantiate(type.args[0], table, state)
        b, state = instantiate(type.args[1], table, state)
        return transform.TApp(a, b), state
    elif type.tag == 2: #TName = lambda name:         obj.Data(2, [name])
        return type, state
    else:
        raise obj.RuntimeTypeError()

def instantiate_constraints(data, table, state):
    constraints = []
    for c in obj.to_list(data):
        c = obj.to_data(c)
        con = c.args[0]
        datum = obj.to_data(c.args[1])
        nargs = []
        for arg in datum.args:
            arg, state = instantiate(arg, table, state)
            nargs.append(arg)
        constraints.append(obj.Data(0, [con, obj.Data(0, nargs)]))
    return constraints, state

class append(Combinator):
    def __init__(self, x, y, xy):
        self.x = x
        self.y = y
        self.xy = xy

    def go(self, state):
        x, y, xy = self.x, self.y, self.xy
        a, state = fresh(state)
        xs, state = fresh(state)
        xys, state = fresh(state)
        case1 = conj(eq(x, Nil), eq(y, xy))
        case2 = conj(
            conj(
                eq(x, Cons(a,xs)),
                eq(xy, Cons(a,xys))),
            append(xs, y, xys))
        return disj(case1, case2).go(state)

def resolve(term, constraints, invocations, types, envc, instances, enums):
    term = obj.to_data(term)
    if term.tag == 0: #Var  = lambda index:        obj.Data(0, [obj.from_integer(index)])
        return term
    elif term.tag == 1: #App  = lambda fn, arg:      obj.Data(1, [fn, arg])
        a = resolve(term.args[0], constraints, invocations, types, envc, instances, enums)
        b = resolve(term.args[1], constraints, invocations, types, envc, instances, enums)
        return transform.App(a, b)
    elif term.tag == 2: #Abs  = lambda body:         obj.Data(2, [body])
        a = resolve(term.args[0], constraints, invocations, types, envc+1, instances, enums)
        return transform.Abs(a)
    elif term.tag == 3: #Let  = lambda bind, body:   obj.Data(3, [bind, body])
        a = resolve(term.args[0], constraints, invocations, types, envc, instances, enums)
        b = resolve(term.args[1], constraints, invocations, types, envc+1, instances, enums)
        return transform.Let(a, b)
    elif term.tag == 4: #Invoke = lambda name:       obj.Data(4, [name])
        type = invocations[term]
        name = obj.to_string(term.args[0])
        tr = obj.to_data(types[name])
        state = empty()
        table = {}
        t, state = instantiate(tr.args[1], table, state)
        cnr, state = instantiate_constraints(tr.args[0], table, state)
        nstates = eq(type, t).go(state)
        if len(nstates) != 1:
            raise obj.RuntimeTypeError()
        state = nstates[0]
        #import os
        #os.write(2, "resolving %s\n" % walk(t, state.subst).rep())
        for c in cnr:
            c = obj.to_data(walk(c, state.subst))
            mysig = obj.to(c.args[0], ConstraintSignature)
            mydat = obj.to_data(c.args[1])
            resolver = get_resolver(mysig, mydat, instances, constraints, envc)
            term = transform.App(term, resolver)
        #os.write(2, "resolved %s\n" % walk(t, state.subst).rep())
        return term
    elif term.tag == 5: #Const = lambda const:       obj.Data(5, [const])
        return term
    elif term.tag == 6: #Case = lambda bind,cases:   obj.Data(6, [bind,cases])
        bind = resolve(term.args[0], constraints, invocations, types, envc, instances, enums)
        by_index = {}
        for case in obj.to_list(term.args[1]):
            index = enums[obj.to_string(case.args[0])].index
            if index in by_index:
                raise obj.RuntimeTypeError()
            by_index[index] = case
        cases = []
        for index in range(len(by_index)):
            case = by_index[index]
            arity = obj.to_integer(case.args[1])
            nterm = resolve(case.args[2], constraints, invocations, types, envc+arity, instances, enums)
            cases.append(transform.Cell(case.args[0], case.args[1], nterm))
        return transform.Case(bind, obj.from_list(cases))
    elif term.tag == 7: #Cocase = lambda cases:      obj.Data(7, [cases])
        by_index = {}
        for case in obj.to_list(term.args[0]):
            index = enums[obj.to_string(case.args[0])].index
            if index in by_index:
                raise obj.RuntimeTypeError()
            by_index[index] = case
        cases = []
        for index in range(len(by_index)):
            case = by_index[index]
            arity = obj.to_integer(case.args[1])
            nterm = resolve(case.args[2], constraints, invocations, types, envc+arity, instances, enums)
            cases.append(transform.Cell(case.args[0], case.args[1], nterm))
        return transform.Cocase(obj.from_list(cases))
    elif term.tag == 8: #ScopeWalk = lambda term:    obj.Data(8, [term])
        a = resolve(term.args[0], constraints, invocations, types, envc, instances, enums)
        return transform.ScopeWalk(a)
    else:
        raise obj.RuntimeTypeError()

def get_resolver(mysig, mydat, instances, constraints, envc):
    #import os
    #os.write(2, "resolve %s %s\n" % (mysig.rep(), mydat.rep()))
    for sig, arity, pat, ident, dep in instances:
        if sig != mysig:
            continue
        bindings = match(mydat, pat, {})
        if bindings is None:
            continue
        args = make_args(arity, bindings)
        resolver = transform.Invoke(ident)
        for dp in obj.to_list(dep.enter(args)):
            dp = obj.to_data(dp)
            msig = obj.to(dp.args[0], ConstraintSignature)
            mdat = obj.to_data(dp.args[1])
            resolver = transform.App(
                resolver,
                get_resolver(msig, mdat, instances, constraints, envc))
        return resolver
    constraints = obj.to_list(constraints)
    index = envc + len(constraints)
    for d in constraints:
        index -= 1
        sig = obj.to(d.args[0], ConstraintSignature)
        pat = obj.to_data(d.args[1])
        if sig != mysig:
            continue
        bindings = match(mydat, pat, {})
        if bindings is None:
            continue
        return transform.Var(index)
    raise obj.RuntimeTypeError()
