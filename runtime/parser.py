# -*- encoding: utf-8 -*-
from parser_table import state, rstate, keywords
import obj
import os

class Tokenizer:
    def __init__(self, parser):
        self.state = 'st_0'
        self.column = 1
        self.line   = 1
        self.pos = (1,1)
        self.inp = []
        self.parser = parser

def st_0(tok, ch):
    if ch in u"0123456789":
        tok.pos = (tok.column, tok.line)
        tok.inp.append(ch)
        tok.state = 'st_digits'
    elif ch in keywords:
        tok.parser.advance(u'"' + ch + u'"', obj.from_string(ch),
            (tok.column, tok.line), (tok.column+1, tok.line))
    elif ch == u" " or ch == u"\n" or ch == u"\t" or ch == u"\r" or ch == u"":
        pass
    elif ch == u'"':
        tok.pos = (tok.column, tok.line)
        tok.state = 'st_string'
    elif ch == u"#":
        tok.state = 'st_comment'
    else:
        tok.pos = (tok.column, tok.line)
        tok.inp.append(ch)
        tok.state = 'st_word'

def st_comment(tok, ch):
    if ch == u"\n":
        tok.state = 'st_0'

def st_word(tok, ch):
    if ch in u"0123456789":
        isalpha = True
    elif ch in keywords:
        isalpha = False
    elif ch == u" " or ch == u"\n" or ch == u"\t" or ch == u"\r" or ch == u"":
        isalpha = False
    elif ch == u'"':
        isalpha = False
    elif ch == u"#":
        isalpha = False
    else:
        isalpha = True
    if isalpha:
        tok.inp.append(ch)
    else:
        text = u"".join(tok.inp)
        if text in keywords:
            tok.parser.advance(u'"' + text + u'"', obj.from_string(text),
                tok.pos, (tok.column+1, tok.line))
        else:
            tok.parser.advance(u'id', obj.from_string(text),
                tok.pos, (tok.column+1, tok.line))
        tok.inp = []
        tok.state = 'st_0'
        st_0(tok, ch)

def st_digits(tok, ch):
    if ch in u"0123456789":
        tok.inp.append(ch)
    elif ch == u".":
        tok.inp.append(ch)
        tok.state = 'st_digits2'
    else:
        tok.parser.advance(u'integer', obj.from_string(u"".join(tok.inp)),
            tok.pos, (tok.column+1, tok.line))
        tok.inp = []
        tok.state = 'st_0'
        st_0(tok, ch)

def st_digits2(tok, ch):
    if ch in u"0123456789":
        tok.inp.append(ch)
    else:
        tok.parser.advance(u'real', obj.from_string(u"".join(tok.inp)),
            tok.pos, (tok.column+1, tok.line))
        tok.inp = []
        tok.state = 'st_0'
        st_0(tok, ch)

def st_string(tok, ch):
    if ch == u'"':
        tok.parser.advance(u'string', obj.from_string(u"".join(tok.inp)),
            tok.pos, (tok.column,tok.line))
        tok.inp = []
        tok.state = 'st_0'
    elif ch == u'\n':
        tok.parser.advance(u'string', obj.from_string(u"".join(tok.inp)),
            tok.pos, (tok.column,tok.line))
        tok.inp = []
        tok.state = 'st_0'
    elif ch == u'\\':
        tok.inp.append(ch)
        tok.state = 'st_string_esc'
    else:
        tok.inp.append(ch)

def st_string_esc(tok, ch):
    tok.inp.append(ch)
    tok.state = 'st_string'

# Collects every 'st_' into a dictionary.
tokenize_n = dict((k,v) for k,v in globals().items()
    if k.startswith('st_'))

def tokenize(tok, ch):
    tokenize_n[tok.state](tok, ch)
    if ch == u"\n":
        tok.line += 1
        tok.column = 1
    else:
        tok.column += 1

# The parsing step
class Parser:
    def __init__(self):
        self.stack = []
        self.top = 0
        self.layout = 0
        self.left = 1
        self.output = None

    def get_action(p, sym, left, line):
        try:
            if p.layout < left or sym == u"":
                return state[p.top][sym]
            else:
                return state[p.top][u'wfb']
        except KeyError:
            if sym == u"":
                sym = u"eof"
            raise ReadError(sym, left, line)

    def advance(p, sym, text, start, stop):
        import os
        os.write(2, "advance %s %s\n" % (sym.encode('utf-8'), text.rep()))
        arg = p.get_action(sym, start[0], start[1])
        while arg[0] == 1:
            lhs, count = rstate[arg[1]]
            objects = []
            for _ in range(count):
                p.top, p.layout, p.left, obj = p.stack.pop()
                objects.append(obj)
            objects.reverse()
            reduced_object = reduction(arg[1], objects)
            if lhs == u"":
                p.stack = []
                p.top = 0
                p.layout = 0
                p.left = 1
                # the 'accept' behavior
                p.output = objects[0]
                return
            else:
                arg = state[p.top][lhs]
                assert arg[0] != 1
                p.stack.append((p.top, p.layout, p.left, reduced_object))
                p.top = arg[1]
                if  arg[0] & 2 != 0:
                    p.layout = p.left
                arg = p.get_action(sym, start[0], start[1])
        if arg[0] & 4 != 0 and p.left != start[0]:
            raise ReadError(u"layout", start[0], start[1])
        p.stack.append((p.top, p.layout, start[0], text))
        p.top = arg[1]
        p.left = start[0]
        if arg[0] & 2 != 0:
            p.layout = start[0]

#lexemes id, integer, real, string
# data File
File = lambda headers, contents: obj.Data(0, [headers, contents])
# data Header
Import = lambda ident, names: obj.Data(0, [ident, names])
Export = lambda names: obj.Data(1, [names])
# data Renaming
Renaming = lambda fro,to: obj.Data(0, [fro,to])
# data Statements
TypeDecl = lambda name, const, type: obj.Data(0, [name, const, type])
Decl = lambda name, term: obj.Data(1, [name, term])
DataDecl = lambda name, parms, strucs: obj.Data(2, [name, parms, strucs])
CodataDecl = lambda name, parms, strucs: obj.Data(3, [name, parms, strucs])
ClassDecl = lambda head, strucs: obj.Data(4, [head, strucs])
DeriveDecl = lambda head: obj.Data(5, [head])
InstanceDecl = lambda head, impls: obj.Data(5, [head, impls])

ClassHead = lambda const, head: obj.Data(0, [const, head])

Impl = lambda name,body: obj.Data(0, [name,body])

Structor = lambda name,parms: obj.Data(0, [name,parms])

# data Term
Name = lambda name: obj.Data(0, [name])
Call = lambda fn,arg: obj.Data(1, [fn,arg])
Abstract = lambda name,body: obj.Data(2, [name,body])
Bind = lambda name,bind,body: obj.Data(3, [name,bind,body])
IntegerConst = lambda num: obj.Data(4, [num])
RealConst = lambda num: obj.Data(5, [num])
StringConst = lambda string: obj.Data(6, [string])
BigCase = lambda term,cases: obj.Data(7, [term, cases])
BigCocase = lambda cases: obj.Data(8, [cases])
ScopedGoal = lambda term: obj.Data(9, [term])

# data Cases
CaseEntry = lambda binders,term: obj.Data(0, [binders, term])

# data List a
Nil = obj.Data(0, [])
Cons = lambda x, xs: obj.Data(1, [x, xs])

unary_call = lambda n, a: Call(Name(obj.from_string(n)), a)
binary_call = lambda n, a, b: Call(Call(Name(obj.from_string(n)), a), b)

def reduction(rule, args):
    if rule == 0:
        return args[0]
    elif rule == 1: #file: headers contents
        return File(args[0], args[1])
    elif rule == 2: #headers:
        return Nil
    elif rule == 3: #headers: header headers
        return Cons(args[0], args[1])
    elif rule == 4: #header: "import" id
        return Import(args[1], Nil)
    elif rule == 5: #      | "import" id "using" names
        return Import(args[1], args[3])
    elif rule == 6: #      | "export" names
        return Export(args[1])
    elif rule == 7: #names: name
        return Cons(args[0], Nil)
    elif rule == 8: #     | name "," names
        return Cons(args[0], args[2])
    elif rule == 9: #name: id
        return Renaming(args[0], args[0])
    elif rule == 10: #    | id "⇒" id
        return Renaming(args[0], args[2])
    elif rule == 11: #contents: WFB stmt
        return Cons(args[0], Nil)
    elif rule == 12: #contents: contents VALIGN WFB stmt
        return Cons(args[1], args[0])
    elif rule == 13: #stmt: id ":" type
        return TypeDecl(args[0], Nil, args[2])
    elif rule == 14: #stmt: id ":" constraints "⇒" type
        return TypeDecl(args[0], args[2], args[4])
    elif rule == 15: #stmt: id binders0 "=" term
        return Decl(args[0], lambda_handler(args[1], args[3]))
    elif rule == 16: #stmt: "data" id binders0
        return DataDecl(args[1], args[2], Nil)
    elif rule == 17: #stmt: "data" id binders0 "where" structors
        return DataDecl(args[1], args[2], args[4])
    elif rule == 18: #stmt: "codata" id binders0 "where" structors
        return CodataDecl(args[1], args[2], args[4])
    elif rule == 19: #stmt: "class" classrow "where" structors
        return ClassDecl(args[1], args[3])
    elif rule == 20: #stmt: "derive" classrow
        return DeriveDecl(args[1])
    elif rule == 21: #stmt: "instance" classrow "where" impls
        return InstanceDecl(args[1], args[3])
    elif rule == 22: #classrow: call
        return ClassHead(Nil, args[0])
    elif rule == 23: #        | constraints "⇒" call
        return ClassHead(args[0], args[2])
    elif rule == 24: #impls: WFB impl
        return Cons(args[0], Nil)
    elif rule == 25: #     | impls VALIGN WFB impl
        return Cons(args[1], args[0])
    elif rule == 26: #impl: id binders0 "=" term
        return Impl(args[0], lambda_handler(args[1], args[3]))
    elif rule == 27: #structors: WFB structor
        return Cons(args[0], Nil)
    elif rule == 28: #         | structors VALIGN WFB structor
        return Cons(args[1], args[0])
    elif rule == 29: #structor: id ":" params
        return Structor(args[0], args[2])
    elif rule == 30: #params: disj
        return Cons(args[0], Nil)
    elif rule == 31: #      | disj "→" params
        return Cons(args[0], args[2])
    elif rule == 32: #constraints: call
        return Cons(args[0], Nil)
    elif rule == 33: #           | call "," constraints
        return Cons(args[0], args[2])
    elif rule == 34: #terms: term
        return Cons(args[0], Nil)
    elif rule == 35: #     | term "," terms
        return Cons(args[0], args[2])
    elif rule == 36: #args:
        return Nil
    elif rule == 37: #args: id args
        return Cons(args[0], args[1])
    elif rule == 38: #term: monad
        return args[0]
    elif rule == 39: #type: disj
        return args[0]
    elif rule == 40: #    | disj "→" type
        return Call(Call(Name(obj.from_string(u"→")), args[0]), args[2])
    elif rule == 41: #monad: let
        return args[0]
    elif rule == 42: #     | let ";" monad
        return binary_call(u">>", args[0], args[2])
    elif rule == 43: #     | let ";" id "←" monad
        return binary_call(u">>=", args[0],
                     Abstract(args[2], args[4]))
    elif rule == 44: #let: lambda
        return args[0]
    elif rule == 45: #     | id "is" lambda ";" let
        return Bind(args[0], args[2], args[4])
    elif rule == 46: #lambda: disj
        return args[0]
    elif rule == 47: #      | id "↦" lambda
        return Abstract(args[0], args[2])
    elif rule == 48: #      | "λ" binders "." lambda
        return lambda_handler(args[1], args[3])
    elif rule == 49: #      | "∃" binders "." lambda
        return fresh_handler(args[1], args[3])
    elif rule == 50: #binders0:
        return Nil
    elif rule == 51: #binders0: binders
        return args[0]
    elif rule == 52: #binders: id
        return Cons(args[0], Nil)
    elif rule == 53: #       | id binders
        return Cons(args[0], args[1])
    elif rule == 54: #disj: conj2
        return args[0]
    elif rule == 55: #    | conj2 "⊔" disj
        return binary_call(u"_lb_", args[0], args[2])
    elif rule == 56: #conj2: disj2
        return args[0]
    elif rule == 57: #    | disj2 "⊓" conj2
        return binary_call(u"_hb_", args[0], args[2])
    elif rule == 58: #disj2: conj
        return args[0]
    elif rule == 59: #     | conj "∨" disj2
        return binary_call(u"_or_", args[0], args[2])
    elif rule == 60: #conj: not
        return args[0]
    elif rule == 61: #    | not "∧" conj
        return binary_call(u"_and_", args[0], args[2])
    elif rule == 62: #not: delay
        return args[0]
    elif rule == 63: #   | "¬" not
        return unary_call(u"_not_", args[1])
    elif rule == 64: #delay: equals
        return args[0]
    elif rule == 65: #     | "{" term "}"
        return ScopedGoal(args[1])
    elif rule == 66: #     | "%" equals
        return unary_call(u"_delay_", args[1])
    elif rule == 67: #equals: comp
        return args[0]
    elif rule == 68: #      | comp "<" comp
        return binary_call(u"_lt_", args[0], args[2])
    elif rule == 69: #      | comp ">" comp
        return binary_call(u"_gt_", args[0], args[2])
    elif rule == 70: #      | comp "≤" comp
        return binary_call(u"_le_", args[0], args[2])
    elif rule == 71: #      | comp "≥" comp
        return binary_call(u"_ge_", args[0], args[2])
    elif rule == 72: #      | comp "=" comp
        return binary_call(u"_eq_", args[0], args[2])
    elif rule == 73: #      | comp "≠" comp
        return binary_call(u"_neq_", args[0], args[2])
    elif rule == 74: #comp: add
        return args[0]
    elif rule == 75: #    | add "∘" comp
        return binary_call(u"_comp_", args[0], args[2])
    elif rule == 76: #add: mul
        return args[0]
    elif rule == 77: #   | mul "+" add
        return binary_call(u"_add_", args[0], args[2])
    elif rule == 78: #   | mul "-" add
        return binary_call(u"_sub_", args[0], args[2])
    elif rule == 79: #mul: prefix
        return args[0]
    elif rule == 80: #   | prefix "*" mul
        return binary_call(u"_mul_", args[0], args[2])
    elif rule == 81: #   | prefix "/" mul
        return binary_call(u"_div_", args[0], args[2])
    elif rule == 82: #prefix: exp
        return args[0]
    elif rule == 83: #      | "~" prefix
        return unary_call(u"_invert_", args[1])
    elif rule == 84: #exp: call
        return args[0]
    elif rule == 85: #   | call "^" exp
        return binary_call(u"_exp_", args[0], args[2])
    elif rule == 86: #call: prim
        return args[0]
    elif rule == 87: #    | call prim
        return Call(args[0], args[1])
    elif rule == 88: #prim: id
        return Name(args[0])
    elif rule == 89: #    | "(" term ")"
        return args[1]
    elif rule == 90: #    | "(" "-" term ")"
        return unary_call(u"_neg_", args[2])
    elif rule == 91: #    | "(" op ")"
        return Name(args[1])
    elif rule == 92: #    | integer
        return IntegerConst(args[0])
    elif rule == 93: #    | real
        return RealConst(args[0])
    elif rule == 94: #    | string
        return StringConst(args[0])
    elif rule == 95: #    | "[" "]"
        return Name(obj.from_string(u"nil"))
    elif rule == 96: #    | "[" terms "]"
        return list_handler(args[1], Name(obj.from_string(u"nil")))
    elif rule == 97: #    | "[" terms "|" term "]"
        return list_handler(args[1], args[3])
    elif rule == 98: #    | "case" term "{" cases "}"
        return BigCase(args[1], args[3])
    elif rule == 99: #    | "cocase" "{" cases "}"
        return BigCocase(args[2])
    elif rule == 100: #sterm: term
        return args[0]
    elif rule == 101: #sterm: term "→" sterm
        return Call(Call(Name(obj.from_string(u"→")), args[0]), args[2])
    elif rule == 102: #cases: case
        return Cons(args[0], Nil)
    elif rule == 103: #     | case ";" cases
        return Cons(args[0], args[2])
    elif rule == 104: #case: binders "⇒" lambda
        return CaseEntry(args[0], args[2])
    elif rule == 105: #op: "+"
        return args[0]
    elif rule == 106: #op: "-"
        return args[0]
    elif rule == 107: #op: "*"
        return args[0]
    elif rule == 108: #op: "/"
        return args[0]
    elif rule == 109: #op: "~"
        return args[0]
    elif rule == 110: #op: "^"
        return args[0]
    elif rule == 111: #op: "→"
        return args[0]
    elif rule == 112: #op: "⊔"
        return args[0]
    elif rule == 113: #op: "⊓"
        return args[0]
    elif rule == 114: #op: "∨"
        return args[0]
    elif rule == 115: #op: "∧"
        return args[0]
    elif rule == 116: #op: "¬"
        return args[0]
    elif rule == 117: #op: "∘"
        return args[0]
    elif rule == 118: #op: "="
        return args[0]
    elif rule == 119: #op: "≠"
        return args[0]
    elif rule == 120: #op: "≤"
        return args[0]
    elif rule == 121: #op: "≥"
        return args[0]
    elif rule == 122: #op: "<"
        return args[0]
    elif rule == 123: #op: ">"
        return args[0]
    else:
        assert False

def lambda_handler(seq, tail):
    seq = obj.to_data(seq)
    if seq.tag == 0:
        return tail
    elif seq.tag == 1:
        return Abstract(seq.args[0],
                    lambda_handler(seq.args[1], tail))
    else:
        assert False

def fresh_handler(seq, tail):
    seq = obj.to_data(seq)
    if seq.tag == 0:
        return tail
    elif seq.tag == 1:
        return unary_call(u"fresh",
                    Abstract(seq.args[0],
                        fresh_handler(seq.args[1], tail)))
    else:
        assert False

def list_handler(seq, tail):
    seq = obj.to_data(seq)
    if seq.tag == 0:
        return tail
    elif seq.tag == 1:
        return binary_call(u"cons", seq.args[0],
                    list_handler(seq.args[1], tail))
    else:
        assert False

def read_fd(fd):
    p = Parser()
    tok = Tokenizer(p)
    allText = ""
    while True:
            text = os.read(fd, 4096)
            if len(text) == 0:
                break;
            allText += text
    for char in allText.decode('utf-8'):
        tokenize(tok, char)
    tokenize(tok, u"")
    p.advance(u"", obj.from_string(u""), (0,0), (0,0))
    assert p.output is not None
    return p.output

class ReadError(Exception):
    def __init__(self, ent, x, y):
        self.ent = ent
        self.x = x
        self.y = y

    def rep(self):
        return "When trying to read %s at line %d col %d" % (
                    self.ent, self.y, self.x)

def demonstration(filename):
    fd = os.open(filename, os.O_RDONLY, 0777)
    try:
        output = read_fd(fd)
    except ReadError as e:
        os.write(2, "ReadError: %s\n" % e.rep())
    else:
        print output.rep()

if __name__=="__main__":
    import sys
    demonstration(sys.argv[1])
