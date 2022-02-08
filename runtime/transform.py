# Translation layer
import parser, obj

Var  = lambda index:        obj.Data(0, [obj.from_integer(index)])
App  = lambda fn, arg:      obj.Data(1, [fn, arg])
Abs  = lambda body:         obj.Data(2, [body])
Let  = lambda bind, body:   obj.Data(3, [bind, body])
Invoke = lambda name:       obj.Data(4, [name])
Const = lambda const:       obj.Data(5, [const])
Case = lambda bind,cases:   obj.Data(6, [bind,cases])
Cocase = lambda cases:      obj.Data(7, [cases])
ScopeWalk = lambda term:    obj.Data(8, [term])

Cell = lambda ident, arity, term: obj.Data(0, [ident, arity, term])

def internal_rep(term, env):
    term = obj.to_data(term)
    if term.tag == 0:   #Name = lambda name: obj.Data(0, [name])
        name = obj.to_string(term.args[0])
        if name in env:
            return Var(env.index(name))
        else:
            return Invoke(obj.from_string(name))
    elif term.tag == 1: #Call = lambda fn,arg: obj.Data(1, [fn,arg])
        return App(
            internal_rep(term.args[0], env),
            internal_rep(term.args[1], env))
    elif term.tag == 2: #Abstract = lambda name,body: obj.Data(2, [name,body])
        env = [obj.to_string(term.args[0])] + env
        return Abs(internal_rep(term.args[1], env))
    elif term.tag == 3: #Bind = lambda name,bind,body: obj.Data(3, [name,bind,body])
        bind = internal_rep(term.args[1], env)
        body = internal_rep(term.args[2], [obj.to_string(term.args[0])] + env)
        return Let(bind, body)
    elif term.tag == 4: #IntegerConst = lambda num: obj.Data(4, [num])
        string = obj.to_string(term.args[0])
        num = obj.rbigint.fromstr(string.encode('utf-8'), base=10)
        return App(
            Invoke(obj.from_string(u"fromInteger")),
            Const(obj.Integer(num)))
    elif term.tag == 5: #RealConst = lambda num: obj.Data(5, [num])
        # TODO:
        raise obj.RuntimeTypeError()
    elif term.tag == 6: #StringConst = lambda string: obj.Data(6, [string])
        return App(
            Invoke(obj.from_string(u"fromString")),
            Const(term.args[0]))
    elif term.tag == 7: #BigCase = lambda term,cases: obj.Data(7, [term, cases])
        bind = internal_rep(term.args[0], env)
        cases = []
        for case in obj.to_list(term.args[1]):
            case = obj.to_data(case)
            binders = obj.to_list(case.args[0])
            ident = binders[0]
            arity = len(binders)-1
            cenv = env 
            args = []
            for i in range(arity):
                b = obj.to_string(binders[len(binders) + ~i])
                #b = obj.to_string(binders[i])
                args.append(b)
            cenv = args + cenv
            term = internal_rep(case.args[1], cenv)
            cell = Cell(ident, obj.from_integer(arity), term)
            cases.append(cell)
        return Case(bind, obj.from_list(cases))
    elif term.tag == 8: #BigCocase = lambda cases: obj.Data(8, [cases])
        cases = []
        for case in obj.to_list(term.args[0]):
            case = obj.to_data(case)
            binders = obj.to_list(case.args[0])
            ident = binders[0]
            arity = len(binders)-1
            cenv = env 
            args = []
            for i in range(arity):
                b = obj.to_string(binders[len(binders) + ~i])
                #b = obj.to_string(binders[i])
                args.append(b)
            cenv = args + cenv
            term = internal_rep(case.args[1], cenv)
            cell = Cell(ident, obj.from_integer(arity), term)
            cases.append(cell)
        return Cocase(obj.from_list(cases))
    elif term.tag == 9: #ScopedGoal = lambda term: obj.Data(9, [term])
        term = internal_rep(term.args[0], env)
        return ScopeWalk(term)
    else:
        assert False

def nametable(term, table):
    term = obj.to_data(term)
    if term.tag == 0: #Var  = lambda index:        obj.Data(0, [obj.from_integer(index)])
        return table
    elif term.tag == 1: #App  = lambda fn, arg:      obj.Data(1, [fn, arg])
        table = nametable(term.args[0], table)
        return nametable(term.args[1], table)
    elif term.tag == 2: #Abs  = lambda body:         obj.Data(2, [body])
        return nametable(term.args[0], table)
    elif term.tag == 3: #Let  = lambda bind, body:   obj.Data(3, [bind, body])
        table = nametable(term.args[0], table)
        return nametable(term.args[1], table)
    elif term.tag == 4: #Invoke = lambda name:       obj.Data(4, [name])
        table[obj.to_string(term.args[0])] = None
        return table
    elif term.tag == 5: #Const = lambda const:       obj.Data(5, [const])
        return table
    elif term.tag == 6: # Case
        table = nametable(term.args[0], table)
        for case in obj.to_list(term.args[1]):
            case = obj.to_data(case)
            table = nametable(case.args[2], table)
        return table
    elif term.tag == 7: # Cocase
        for case in obj.to_list(term.args[0]):
            case = obj.to_data(case)
            table = nametable(case.args[2], table)
        return table
    elif term.tag == 8: # ScopeWalk
        return nametable(term.args[0], table)
    else:
        raise obj.RuntimeTypeError()

TVar  = lambda index:        obj.Data(0, [obj.from_integer(index)])
TApp  = lambda fn, arg:      obj.Data(1, [fn, arg])
TName = lambda name:         obj.Data(2, [name])

def type_rep(term, table):
    term = obj.to_data(term)
    if term.tag == 0: #Name = lambda name: obj.Data(0, [name])
        name = obj.to_string(term.args[0])
        if name.startswith(u"$"):
            var = table.get(name, None)
            if var is None:
                table[name] = var = Var(len(table))
            return var
        else:
            return TName(term.args[0])
    elif term.tag == 1: #Call = lambda fn,arg: obj.Data(1, [fn,arg])
        return TApp(
            type_rep(term.args[0], table),
            type_rep(term.args[1], table))
    elif term.tag == 2: #Abstract = lambda name,body: obj.Data(2, [name,body])
        raise obj.RuntimeTypeError()
    elif term.tag == 3: #Bind = lambda name,bind,body: obj.Data(3, [name,bind,body])
        raise obj.RuntimeTypeError()
    elif term.tag == 4: #IntegerConst = lambda num: obj.Data(4, [num])
        raise obj.RuntimeTypeError()
    elif term.tag == 5: #RealConst = lambda num: obj.Data(5, [num])
        raise obj.RuntimeTypeError()
    elif term.tag == 6: #StringConst = lambda string: obj.Data(6, [string])
        raise obj.RuntimeTypeError()
    elif term.tag == 7: #BigCase = lambda term,cases: obj.Data(7, [term, cases])
        raise obj.RuntimeTypeError()
    elif term.tag == 8: #BigCocase = lambda cases: obj.Data(8, [cases])
        raise obj.RuntimeTypeError()
    elif term.tag == 9: #ScopedGoal = lambda term: obj.Data(9, [term])
        raise obj.RuntimeTypeError()
    else:
        raise obj.RuntimeTypeError()

def strongly_connected_components(graph):
    components = []
    # Tarjan's algorithm, copied from wikipedia
    index = 0
    S = []
    indices = {}
    lowlinks = {}
    onStack = {}
    for v in graph.keys():
        if v not in indices:
            index = _strongconnect_(v, graph, components, index, S, indices, lowlinks, onStack)

    return components

def _strongconnect_(v, graph, components, index, S, indices, lowlinks, onStack):
    # Set the depth index for v to the smallest unused index
    indices[v] = index
    lowlinks[v] = index
    index += 1
    S.append(v)
    onStack[v] = None
    # Consider successors of v
    for w in graph.get(v, {}):
        if w not in indices:
            # Successor w has not yet been visited; recurse on it
            index = _strongconnect_(w, graph, components, index, S, indices, lowlinks, onStack)
            lowlinks[v] = min(lowlinks[v], lowlinks[w])
        elif w in onStack:
            # Successor w is in stack S and hence in the current SCC
            # If w is not on stack, then (v, w) is an edge pointing to
            # an SCC already found and must be ignored
            # Note: The next line may look odd - but is correct.
            # It says w.index not w.lowlink; that is deliberate and from the original paper
            lowlinks[v] = min(lowlinks[v], indices[w])
     # If v is a root node, pop the stack and generate an SCC
    if lowlinks[v] == indices[v]:
        # start a new strongly connected component
        component = []
        while True:
            w = S.pop()
            onStack.pop(w)
            component.append(w)
            if w == v:
                break
        components.append(component)
    return index
