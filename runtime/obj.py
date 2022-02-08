from rpython.rlib.rbigint import rbigint
from rpython.rlib.objectmodel import specialize

class Object(object):
    def enter(self, args):
        if len(args) == 0:
            return self
        else:
            raise RuntimeTypeError()

    def rep(self):
        return "object"

class RuntimeTypeError(Exception):
    pass

class Var(Object):
    def __init__(self, key):
        self.key = key

    def rep(self):
        return "Var%d" % self.key

class Integer(Object):
    def __init__(self, number):
        self.number = number
    
    def rep(self):
        return self.number.format("0123456789")

class String(Object):
    def __init__(self, string):
        self.string = string

    def rep(self):
        return '"' + str(self.string.encode('utf-8')) + '"'

class Data(Object):
    def __init__(self, tag, args):
        self.tag = tag
        self.args = args

    def rep(self):
        narg = []
        for arg in self.args:
            narg.append(arg.rep())
        return str(self.tag) + "{" + ", ".join(narg) + "}"

#class Codata(Object):
#    def __init__(self, opts):
#        self.opts = opts
#
#    def rep(self):
#        return "codata/%d" % len(self.opts)

def from_integer(intval):
    return Integer(rbigint.fromint(intval))

def to_integer(value):
    return to_bigint(value).toint()

def to_bigint(value):
    result = value.enter([])
    if isinstance(result, Integer):
        return result.number
    else:
        raise RuntimeTypeError()

def to_data(value):
    result = value.enter([])
    if isinstance(result, Data):
        return result
    else:
        raise RuntimeTypeError()

#def to_codata(value):
#    result = value.enter([])
#    if isinstance(result, Codata):
#        return result
#    else:
#        raise RuntimeTypeError()

def from_list(lst):
    head = Data(0, [])
    for arg in reversed(lst):
        head = Data(1, [arg, head])
    return head

def to_list(value):
    data = to_data(value)
    out = []
    while data.tag == 1 and len(data.args) == 2:
        out.append(data.args[0])
        data = to_data(data.args[1])
    if data.tag == 0 and len(data.args) == 0:
        return out
    else:
        raise RuntimeTypeError()

def from_string(string):
    return String(string)

def to_string(value):
    result = value.enter([])
    if isinstance(result, String):
        return result.string
    else:
        raise RuntimeTypeError()

@specialize.arg(1)
def to(value, type):
    result = value.enter([])
    if isinstance(result, type):
        return result
    else:
        raise RuntimeTypeError()
    
true = Data(1, [])
false = Data(0, [])

def from_bool(boolean):
    if boolean:
        return true
    else:
        return false

def to_bool(value):
    return to_data(value).tag > 0

@specialize.call_location()
def call(value, *args):
    return value.enter(list(reversed(args)))
