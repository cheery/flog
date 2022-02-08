import core
import evaluator
import inference
import obj
import os
import parser
import transform
import ukanren

And = ukanren.ConstraintSignature(u"And", 1)
Lb = ukanren.ConstraintSignature(u"Lb", 1)
FromInteger = ukanren.ConstraintSignature(u"FromInteger", 1)

class classMethod(obj.Object):
    def __init__(self, classIndex):
        self.classIndex = classIndex

    def enter(self, args):
        instance = obj.to_data(args.pop())
        return instance.args[self.classIndex].enter(args)

class DataType:
    def __init__(self, name, codata, cases):
        self.name = name
        self.codata = codata
        self.cases = cases

class EnumPoint:
    def __init__(self, datatype, index):
        self.datatype = datatype
        self.index = index

class Enum(obj.Object):
    def __init__(self, index, arity, co=False):
        self.index = index
        self.arity = arity
        self.co = co

    def enter(self, args):
        if len(args) < self.arity:
            return evaluator.PAP(evaluator.Prog({}, [], self), args)
        elif len(args) == self.arity:
            if self.co:
                stream = obj.to_data(args[len(args)-1])
                return stream.args[self.index].enter(args)
            else:
                args.reverse()
                return obj.Data(self.index, args)
        else:
            raise obj.RuntimeTypeError()

def entry_point(config):
    def main(argv):
        core.init_executioncontext(config)
        exit_status = 0
        try:
            filename = argv[1]
        except IndexError:
            load_fd(0)
        else:
            fd = os.open(filename, os.O_RDONLY, 0777)
            load_fd(fd)
            os.close(fd)
        return exit_status
    return main

def normalize_constraints(constraints):
    names = {u"dummy": ukanren.tt}
    rules = []
    rules.append(ukanren.Rule(
        arity = 1,
        keep = [
            (FromInteger, obj.Data(0, [ukanren.Hole(0)])),
        ],
        remove = [
            (FromInteger, obj.Data(0, [ukanren.Hole(0)])),
        ],
        guard = ukanren.always_true,
        body = evaluator.activate(names, [],
            transform.Abs(transform.Const(ukanren.tt)))))
    rules.append(ukanren.Rule(
        arity = 0,
        keep = [
        ],
        remove = [
            (FromInteger, obj.Data(0, [transform.TName(obj.from_string(u"Integer"))])),
        ],
        guard = ukanren.always_true,
        body = ukanren.tt))
    state = ukanren.empty(rules)
    goal = ukanren.tt
    for data in constraints:
        data = obj.to_data(data)
        sig = data.args[0]
        term = data.args[1]
        goal = ukanren.conj(goal, ukanren.constraint(sig, term.args))
    nstates = goal.go(state)
    if len(nstates) == 1:
        return ukanren.get_constraints(nstates[0])
    raise obj.RuntimeTypeError()

def make_type(index, datatype):
    _, args, retype = datatype.cases[index]
    for arg in reversed(args):
        retype = inference.arrow(arg, retype)
    return obj.Data(0, [obj.from_list([]), retype])

def load_fd(fd):
    output = obj.to_data(parser.read_fd(fd))
    assert output.tag == 0 # File
    headers = obj.to_list(output.args[0])
    contents = obj.to_list(output.args[1])
    constraints_tab = {}
    reps = {}
    depends = {}
    types = {}
    names = {}
    enums = {}

    ListT = DataType(u"List", False, [
        (u"nil", [], transform.TApp(
                        transform.TName(obj.from_string(u"List")),
                        transform.TVar(0))),
        (u"cons", [
            transform.TVar(0),
            transform.TApp(transform.TName(obj.from_string(u"List")),
                           transform.TVar(0))
            ], transform.TApp(
                    transform.TName(obj.from_string(u"List")),
                    transform.TVar(0)))
    ])
    types[u"nil"] = make_type(0, ListT)
    enums[u"nil"] = EnumPoint(ListT, 0)
    names[u"nil"] = Enum(0, 0, co=False)

    types[u"cons"] = make_type(1, ListT)
    enums[u"cons"] = EnumPoint(ListT, 1)
    names[u"cons"] = Enum(1, 2, co=False)
    StreamT = DataType(u"Stream", True, [
        (u"hd", [
            transform.TApp(transform.TName(obj.from_string(u"Stream")),
                           transform.TVar(0))
                 ], transform.TVar(0)),
        (u"tl", [
            transform.TApp(transform.TName(obj.from_string(u"Stream")),
                           transform.TVar(0))
            ], transform.TApp(
                    transform.TName(obj.from_string(u"Stream")),
                    transform.TVar(0)))
    ])
    types[u"hd"] = make_type(0, StreamT)
    enums[u"hd"] = EnumPoint(StreamT, 0)
    names[u"hd"] = Enum(0, 1, co=True)

    types[u"tl"] = make_type(1, StreamT)
    enums[u"tl"] = EnumPoint(StreamT, 1)
    names[u"tl"] = Enum(1, 1, co=True)

        

    constraints_tab[u"And"] = And
    constraints_tab[u"Lb"] = Lb
    constraints_tab[u"FromInteger"] = FromInteger

    names[u"integerFromInteger"] = obj.Data(0, [
        evaluator.activate(names, [], transform.Abs(transform.Var(0)))
        ])
    instances = [
        (FromInteger,
            0, # Arity
            obj.Data(0, [transform.TName(obj.from_string(u"Integer"))]),
            obj.from_string(u"integerFromInteger"),
            obj.from_list([]))
    ]
    # populate env.
    #class And a where
    #    and : a → a → a
    #
    # _and_ : And a ⇒ a → a → a
    
    #class Lb a where
    #    _lb_ : a → a → a
    #
    # _lb_ : Lb a ⇒ a → a → a
    a = transform.TVar(0)
    names[u"_and_"] = classMethod(0)
    types[u"_and_"] = obj.Data(0, [
        obj.from_list([obj.Data(0, [And, obj.Data(0, [a])])]),
        inference.arrow(a, inference.arrow(a, a)) 
        ])
    names[u"_lb_"] = classMethod(0)
    types[u"_lb_"] = obj.Data(0, [
        obj.from_list([obj.Data(0, [Lb, obj.Data(0, [a])])]),
        inference.arrow(a, inference.arrow(a, a)) 
        ])
    names[u"fromInteger"] = classMethod(0)
    types[u"fromInteger"] = obj.Data(0, [
        obj.from_list([obj.Data(0, [FromInteger, obj.Data(0, [a])])]),
        inference.arrow(transform.TName(obj.from_string(u"Integer")), a)
        ])


    #main = None
    for entry in contents:
        if entry.tag == 0: # TypeDecl
            table = {}
            name = obj.to_string(entry.args[0])
            co = []
            for term in obj.to_list(entry.args[1]):
                term = obj.to_data(transform.type_rep(term, table))
                args = []
                while term.tag == 1:
                    args.insert(0, term.args[1])
                    term = obj.to_data(term.args[0])
                if term.tag == 2:
                    n = obj.to_string(term.args[0])
                    c = constraints_tab.get(n, None)
                    if c is None:
                        raise obj.RuntimeTypeError()
                    else:
                        co.append(obj.Data(0, [c, obj.Data(0, args)]))
                else:
                    raise obj.RuntimeTypeError()
            type = transform.type_rep(entry.args[2], table)
            types[name] = obj.Data(0, [obj.from_list(co), type])
        elif entry.tag == 1: # Decl
            name = obj.to_string(entry.args[0])
            rep = transform.internal_rep(entry.args[1], [])
            if name in reps or name in names:
                raise obj.RuntimeTypeError()
            reps[name] = rep
            depends[name] = transform.nametable(rep, {})

    components = transform.strongly_connected_components(depends)
    index = 0
    for component in components:
        os.write(1, "component %d\n" % index)
        for name in component:
            os.write(1, "  %s\n" % name.encode('utf-8'))
        index += 1

    for component in components:
        if len(component) == 1 and component[0] not in reps:
            continue

        had_type = {}
        state = ukanren.empty()
        for name in component:
            if name not in types:
                a, state = ukanren.fresh(state)
                types[name] = obj.Data(0, [parser.Nil, a])
            else:
                had_type[name] = None
                os.write(1, "%s : %s\n" % (name.encode('utf-8'), types[name].rep()))

        goal = ukanren.tt
        all_constraints = parser.Nil
        invocations = {}
        for name in component:
            constraints, state = ukanren.fresh(state)
            nall_constraints, state = ukanren.fresh(state)
            local_invocations = {}
            goal = ukanren.conj(goal,
                inference.InferCode(types, [], reps[name], constraints,
                    types[name].args[1], local_invocations, enums))
            goal = ukanren.conj(goal,
                inference.append(constraints, all_constraints, nall_constraints))
            all_constraints = nall_constraints
            invocations[name] = local_invocations
        nstates = goal.go(state)
        if len(nstates) == 1:
            constraints = ukanren.walk(all_constraints, nstates[0].subst)
            constraints = normalize_constraints(obj.to_list(constraints))
            for name in component:
                table = {}
                if name not in had_type:
                    types[name] = obj.Data(0, [
                        inference.generalize_constraints(constraints, table),
                        inference.generalize(ukanren.walk(types[name].args[1], nstates[0].subst), table)])
                    os.write(1, "%s : %s\n" % (name.encode('utf-8'), types[name].rep()))
                local_invocations = invocations[name]
                os.write(1, "invocation points\n")
                nlocal_invocations = {}
                for term, type in local_invocations.iteritems():
                    type = ukanren.walk(type, nstates[0].subst)
                    type = inference.generalize(type, table)
                    nlocal_invocations[term] = type
                    os.write(1, "  %s : %s\n" % (term.rep(), type.rep()))
                #rterm = ukanren.walk(rterms[name], nstates[0].subst)
                rterm = inference.resolve(reps[name],
                    types[name].args[0],
                    nlocal_invocations,
                    types,
                    0,
                    instances,
                    enums)
                for _ in constraints:
                    rterm = transform.Abs(rterm)
                os.write(1, "%s = %s\n" % (name.encode('utf-8'), rterm.rep()))
                names[name] = evaluator.activate(names, [], rterm)
        else:
            for name in component:
                types.pop(name)


    main = names.get(u"main", None)
    if main is not None:
        #names = {} # TODO: Add names -bin.
        #names[u"main"] = thunk = evaluator.activate(names, [], main)
        result = main.enter([])
        os.write(1, "Returned %s\n" % result.rep())

def target(driver, args):
    driver.exe_name = "flog"
    return entry_point(driver.config), None

if __name__=="__main__":
    from rpython.config.translationoption import get_combined_translation_config
    import sys
    config = get_combined_translation_config(translating=True)
    sys.exit(entry_point(config)(sys.argv))
