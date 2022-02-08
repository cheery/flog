import obj
import transform

# An unevaluated expression.
class Prog(obj.Object):
    def __init__(self, names, env, body):
        self.names = names
        self.env = env
        self.body = body
    
    def enter(self, args):
        return evaluate(self.names, self.env, self.body, args)

    def rep(self):
        return "prog"

# Implements lazy evaluation.
# Upon evaluation, the thunk rewrites itself into the evaluation result.
class Thunk(obj.Object):
    def __init__(self, ref):
        self.ref = ref

    def enter(self, args):
        if self.ref is None:
            raise obj.RuntimeTypeError() # Blackholed reference
        ref, self.ref = self.ref, None
        self.ref = ref.enter([])
        return self.ref.enter(args)

    def rep(self):
        return "thunk"

# Produced whenever a function is entered with too few arguments.
class PAP(obj.Object):
    def __init__(self, fun, args):
        self.fun = fun
        self.args = args

    def enter(self, args):
        args.extend(self.args)
        return self.fun.enter(args)

    def rep(self):
        return "PAP"

def activate(names, env, expr):
    data = obj.to_data(expr)
    if data.tag == 0:   # Var
        return lookup(env, obj.to_integer(data.args[0]))
    elif data.tag == 1: # App
        if examine(data):
            return evaluate(names, env, data, [])
        else:
            return Thunk(Prog(names, env, data))
    elif data.tag == 2: # Abs
        return Prog(names, env, data)
    elif data.tag == 3: # Let
        binds = obj.to_list(data.args[0])
        bound_env = []
        for bind in binds:
            bound_env.append(activate(names, env, bind))
        env = env + bound_env
        return activate(names, env, data.args[1])
    elif data.tag == 4: # Invoke
        return Prog(names, env, data)
    elif data.tag == 5: # Const
        return data.args[0]
    elif data.tag == 6: # Case
        return Prog(names, env, data)
    elif data.tag == 7: # Cocase
        return Prog(names, env, data)
    elif data.tag == 8: # ScopeWalk
        return Prog(names, env, data)
    else:
        raise obj.RuntimeTypeError()

def examine(data):
    if data.tag == 0: # Var
        return False
    elif data.tag == 1: # App
        return examine(data.args[0])
    elif data.tag == 2: # Abs
        return False
    elif data.tag == 3: # Let
        return examine(data.args[1])
    elif data.tag == 4: # Invoke
        return True
    elif data.tag == 5: # Const
        return False
    elif data.tag == 6: # Case
        return True
    elif data.tag == 7: # CoCase
        return True
    elif data.tag == 8: # ScopeWalk
        return True
    else:
        raise obj.RuntimeTypeError()

def evaluate(names, env, expr, args):
    data = obj.to_data(expr)
    if data.tag == 0: # Var
        return lookup(env, obj.to_integer(data.args[0])).enter(args)
    elif data.tag == 1: # App
        fn = data.args[0]
        arg = data.args[1]
        args.append(activate(names, env, arg))
        return evaluate(names, env, fn, args)
    elif data.tag == 2: # Abs
        try:
            env = env + [args.pop()]
        except IndexError:
            return PAP(Prog(names, env, data), args)
        return evaluate(names, env, data.args[0], args)
    elif data.tag == 3: # Let
        env = env + [activate(names, env, data.args[0])]
        return evaluate(names, env, data.args[1], args)
    elif data.tag == 4: # Invoke
        name = obj.to_string(data.args[0])
        return names[name].enter(args)
    elif data.tag == 5: # Const
        return data.args[0].enter(args)
    elif data.tag == 6: # Case
        seq  = obj.to_list(data.args[1])
        data = obj.to_data(activate(names, env, data.args[0]))
        if data.tag < len(seq) and obj.to_integer(seq[data.tag].args[1]) == len(data.args):
            env = env + data.args
            return evaluate(names, env, seq[data.tag].args[2], args)
        else:
            raise obj.RuntimeTypeError()
    elif data.tag == 7: # CoCase
        seq  = obj.to_list(data.args[0])
        args = []
        for case in seq:
            case = obj.to_data(case)
            arity = obj.to_integer(case.args[1])
            term = case.args[2]
            for _ in range(arity):
                term = transform.Abs(term)
            args.append(activate(names, env, term))
        return obj.Data(0, args)
    elif data.tag == 8: # ScopeWalk
        raise obj.RuntimeTypeError() # TODO:
    else:
        raise obj.RuntimeTypeError()

def lookup(env, index):
    if 0 <= index < len(env):
        return env[len(env) + ~index]
    else:
        raise obj.RuntimeTypeError()
