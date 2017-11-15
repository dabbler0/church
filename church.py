from collections import namedtuple

'''
TOKENIZER
=========

Generally, the tokenizer works by matching tokens at the beginning of
the line, consuming them and any following whitespace, and recursing
on the rest of the line.

A token matched at the beginning of a line consists either of a single paren
('(' or ')'), a comment (';' through a newline), or an atom (anything until whitespace,
a paren, or the start of a comment).

Comment tokens are skipped, however.
'''
def tokens(source):
    # We've reached the end.
    if len(source) == 0:
        return

    # Parens and dots
    if source[0] in '().':
        i = 1
        yield source[:i]

    # Comments
    elif source[0] == ';':
        i = source.index('\n')

    # Atoms
    else:
        i = next(i for i, c in enumerate(source) if c in '()\n ;.')
        yield source[:i]

    # Recurse, skipping whitespace
    yield from tokens(source[i:].lstrip())


def tokenize(source):
    # Wrapper function.
    return list(tokens(source.lstrip() + '\n'))
'''
PARSER
======

Standard top-down recurisve parser style.

There are two kinds of expressions, atoms and s_expressions. An s_expression is either
an atom or a '(' followed by any numebr of s_expressions followed by a ')'.

We use a TokenStream class here to more conveniely facility the top-down recursive
"consuming tokens" style.
'''

class TokenStream:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self, n = 0):
        # Get first token in the stream
        if self.pos + n < len(self.tokens):
            return self.tokens[self.pos + n]
        return None

    def take(self):
        # Pop the first token off the stream (O(1))
        self.pos += 1
        return self.tokens[self.pos - 1]

    def empty(self):
        # Am I at the end of the stream?
        return self.pos == len(self.tokens)

SExpression, LExpression = namedtuple('SExpression', ['head', 'tail']), namedtuple('LExpression', ['param', 'body'])

def primary_expression(tokens):
    # atom . expression
    if tokens.peek(1) == '.':
        var = tokens.take()
        tokens.take()
        return LExpression(var, expression(tokens))

    # ( expression )
    if tokens.peek() == '(':
        tokens.take()

        result = expression(tokens)

        if tokens.peek() == ')':
            tokens.take()
            return result

        raise SyntaxError

    # atom
    return tokens.take()


def expression(tokens):
    # expression primary_expression
    head = primary_expression(tokens)
    while (not tokens.empty()) and tokens.peek() != ')':
        head = SExpression(head, primary_expression(tokens))
    return head

def parse(tokens):
    # Construct a stream
    stream = TokenStream(tokens)

    # Parse from it
    result = expression(stream)

    # If the parser did not consume the
    # entire stream, error out.
    if not stream.empty():
        raise SyntaxError

    return result

'''
EVALUATION
==========

Every expression is either an atom, an SExpression, or an LExpression.

Every node in the tree in Church will be surrounded by a Wrap.

Without any other context, a Wrap will have an eventual value. Wraps
also do not keep track of scope.

The problem comes when we simplify inside functions. How is one to do the following?

y. (x. y. x) y

Here's what we do. Because of the order in which we do stuff, if we are reducing this S-Expression,
the head will already be in normal form.

Also, we are substituting in the head anwyay.

Thus it is harmless to rename all variables named 'y' in the head. So this will become:

y. w. y

Where the *inner* y has been renamed.

(x. x) z

=> z is a Wrap
=> substitute (x) => Wrap z in the body over there
=> get back Wrap z

'''

class SPair:
    def __init__(self, head, tail):
        self.head, self.tail = head, tail
class LPair:
    def __init__(self, param, body):
        self.param, self.body = param, body

vid = 0
def newvar():
    global vid
    vid += 1
    return vid - 1

class IsolationNmap:
    def __init__(self):
        self.map = {}

    def name(self, var):
        global vid
        if var not in self.map:
            self.map[var] = vid
            vid += 1
        return self.map[var]

class PrintMap:
    def __init__(self):
        self.map = {}
        self.cid = 0
        self.chars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'

    def cid_to_name(self, cid):
        if cid < len(self.chars):
            return self.chars[cid]
        return (self.cid_to_name(cid // len(self.chars)) +
                self.chars[cid % len(self.chars)])

    def name(self, var):
        if var not in self.map:
            self.map[var] = self.cid_to_name(self.cid)
            self.cid += 1
        return self.map[var]
class Wrap:
    def __init__(self, pair, normal_form = False):
        self.pair = pair
        self.normal_form = normal_form
        self.contains_cache = {}
        self.variables_cache = None
        self.parameters_cache = None

    def alpha(self, amap):
        '''
        Perform an alpha transformation to avoid
        reusing the given variables.
        '''

        # If we are unchanged, return ourself
        if len(amap.keys() & self.variables()) == 0:
            return self

        if type(self.pair) is int:
            return Wrap(amap[self.pair] if self.pair in amap else self.pair,
                    self.normal_form)

        if type(self.pair) is SPair:
            return Wrap(SPair(
                self.pair.head.alpha(amap),
                self.pair.tail.alpha(amap)
            ), self.normal_form)

        if type(self.pair) is LPair:
            return Wrap(LPair(
                (amap[self.pair.param] if self.pair.param in amap else self.pair.param),
                self.pair.body.alpha(amap)
            ), self.normal_form)

        # If we are wrapping a wrap,
        # take this opportunity to unwrap it.
        if type(self.pair) is Wrap:
            return self.pair.alpha(amap)

    def bind(self, var, value):
        '''
        Substitute returns a *new* Wrap.

        Recall that we guaranteed that, once instantiated,
        a Wrap will always represent an equivalent tree.
        '''

        # For more efficient computation,
        # preserve work across substitutions
        # where possible.
        if var not in self:
            return self

        if type(self.pair) is int:
            if self.pair == var:
                return value
            return self

        if type(self.pair) is SPair:
            return Wrap(SPair(
                self.pair.head.bind(var, value),
                self.pair.tail.bind(var, value)
            ))

        if type(self.pair) is LPair:
            return Wrap(LPair(
                self.pair.param,
                self.pair.body.bind(var, value)
            ))

        # If we are wrapping a wrap,
        # take this opportunity to unwrap it.
        if type(self.pair) is Wrap:
            return self.pair.bind(var, value)

    def __contains__(self, var):
        if var not in self.contains_cache:
            if type(self.pair) is int:
                self.contains_cache[var] = (var == self.pair)
            elif type(self.pair) is Wrap:
                self.contains_cache[var] = var in self.pair
            elif type(self.pair) is SPair:
                self.contains_cache[var] = (var in self.pair.head) or (var in self.pair.tail)
            elif type(self.pair) is LPair:
                self.contains_cache[var] = (var != self.pair.param) and (var in self.pair.body)
        return self.contains_cache[var]

    def variables(self):
        if self.variables_cache is None:
            if type(self.pair) is int:
                self.variables_cache = {self.pair}
            elif type(self.pair) is Wrap:
                self.variables_cache = self.pair.variables()
            elif type(self.pair) is SPair:
                self.variables_cache = self.pair.head.variables() | self.pair.tail.variables()
            elif type(self.pair) is LPair:
                self.variables_cache = {self.pair.param} | self.pair.body.variables()
        return self.variables_cache

    def parameters(self):
        if self.parameters_cache is None:
            if type(self.pair) is int:
                self.parameters_cache = set()
            elif type(self.pair) is Wrap:
                self.parameters_cache = self.pair.parameters()
            elif type(self.pair) is SPair:
                self.parameters_cache = self.pair.head.parameters() | self.pair.tail.parameters()
            elif type(self.pair) is LPair:
                self.parameters_cache = {self.pair.param} | self.pair.body.parameters()
        return self.parameters_cache

    def reduce(self):
        if type(self.pair) is int:
            # An expression that is just a variable
            # is in normal form.
            self.normal_form = True
            return 'close'

        if type(self.pair) is SPair:
            # If the head is in lambda form,
            # or is a wrap of something in lambda form,
            # reduce it once and then substitute.
            hpair = self.pair.head.pair
            hpair = hpair.pair if type(hpair) is Wrap else hpair
            if type(hpair) is LPair:
                amap = {v: newvar() for v in self.pair.tail.parameters()}
                self.pair = hpair.body.alpha(amap).bind(
                    (amap[hpair.param] if hpair.param in amap else hpair.param),
                    self.pair.tail
                )
                return 'beta'

            # Otherwise, try reducing the head.
            if not self.pair.head.normal_form:
                return self.pair.head.reduce()

            # If the head is in normal form and this
            # is not a lambda form, reduce the tail.
            if not self.pair.tail.normal_form:
                return self.pair.tail.reduce()

            # Both the head and tail are fully reduced,
            # so we are fully reduced also.
            self.normal_form = True
            return 'close'

        if type(self.pair) is LPair:
            # Eta-reduce if possible.
            bpair = self.pair.body.pair
            bpair = bpair.pair if type(bpair) is Wrap else bpair
            if (type(bpair) is SPair and type(bpair.tail.pair) is int and
                    self.pair.param == bpair.tail.pair and
                    self.pair.param not in bpair.head):
                self.pair = bpair.head
                return 'eta'

            # Recurse into the body.
            if self.pair.body.normal_form:
                self.normal_form = True
                return 'close'

            return self.pair.body.reduce()

        if type(self.pair) is Wrap:
            # If our child is a Wrap wrapping a Wrap,
            # unwrap it.
            if type(self.pair.pair) is Wrap:
                self.pair = self.pair.pair
                return 'cut'

            # If our child is in normal form, inherit it.
            if self.pair.normal_form:
                self.pair = self.pair.pair
                return 'cut'

            # Otherwise recurse
            return self.pair.reduce()

    def normalize(self, limit = 5000):
        for i in range(limit):
            self.reduce()
            if self.normal_form:
                return

    def print(self, nmap = None, precedence = 'root'):
        if nmap is None:
            nmap = PrintMap()
        if type(self.pair) is int:
            return nmap.name(self.pair)

        if type(self.pair) is Wrap:
            return self.pair.print(nmap, precedence)

        if type(self.pair) is SPair:
            if precedence == 'root':
                return '%s %s' % (self.pair.head.print(nmap, 'left'), self.pair.tail.print(nmap, 'right'))
            if precedence == 'left':
                return '%s %s' % (self.pair.head.print(nmap, 'left'), self.pair.tail.print(nmap, 'right-left'))
            if precedence in ('right', 'right-left'):
                return '(%s %s)' % (self.pair.head.print(nmap, 'left'), self.pair.tail.print(nmap, 'right'))

        if type(self.pair) is LPair:
            if is_t(self):
                return '#t'
            if is_f(self):
                return '#f'
            if is_nil(self):
                return '*nil'

            found, a, b = is_cons(self)
            if found:
                return '<%s %s>' % (a.print(nmap, 'left'), b.print(nmap, 'right'))

            if precedence in ('root', 'right'):
                return '%s. %s' % (nmap.name(self.pair.param), self.pair.body.print(nmap, 'root'))
            if precedence in ('left', 'right-left'):
                return '(%s. %s)' % (nmap.name(self.pair.param), self.pair.body.print(nmap, 'root'))

    def __str__(self):
        return self.print()

def is_t(w):
    return type(w.pair) is LPair and type(w.pair.body.pair) is LPair and w.pair.param == w.pair.body.pair.body.pair
def is_f(w):
    return type(w.pair) is LPair and type(w.pair.body.pair) is LPair and w.pair.body.pair.param == w.pair.body.pair.body.pair
def is_pair(w):
    found = (type(w.pair) is LPair and type(w.pair.body.pair) is SPair and
        type(w.pair.body.pair.head.pair) is SPair and
        w.pair.body.pair.head.pair.head.pair == w.pair.param)
    if found:
        return True, w.pair.body.pair.head.pair.tail, w.pair.body.pair.tail
    else:
        return False, None, None
def is_nil(w):
    pair, a, b = is_pair(w)
    return pair and is_t(a) and is_t(b)
def is_cons(w):
    pair, a, b = is_pair(w)
    if not pair:
        return False, None, None
    pair, a, b = is_pair(b)
    if not pair:
        return False, None, None
    return True, a, b

class WrapNmap:
    def __init__(self):
        self.unbound_map = {}
        self.root = WrapNmapNode(self, None, None, None)

    def name(self, x):
        global vid
        if x not in self.unbound_map:
            self.unbound_map[x] = vid
            vid += 1
        return self.unbound_map[x]

class WrapNmapNode:
    def __init__(self, master, parent, var, value):
        self.master = master
        self.var = var
        self.value = value
        self.parent = parent

    def name(self, x):
        if x == self.var:
            return self.value
        if self.parent is not None:
            return self.parent.name(x)
        return self.master.name(x)

    def fork(self, var):
        global vid
        result = WrapNmapNode(self.master, self, var, vid)
        vid += 1
        return result

def wrapify(tree, nmap = None):
    if nmap is None:
        nmap = WrapNmap().root

    if type(tree) is SExpression:
        return Wrap(SPair(wrapify(tree.head, nmap), wrapify(tree.tail, nmap)))
    if type(tree) is LExpression:
        nmap = nmap.fork(tree.param)
        return Wrap(LPair(nmap.name(tree.param), wrapify(tree.body, nmap)))
    if type(tree) is str:
        return Wrap(nmap.name(tree))

from prompt_toolkit import prompt
from prompt_toolkit.history import InMemoryHistory
from prompt_toolkit.auto_suggest import AutoSuggestFromHistory
from prompt_toolkit.completion import Completer, Completion
import sys

class MacroCompleter(Completer):
    def __init__(self, macros):
        self.macros = macros
    def get_completions(self, document, complete_event):
        line = document.current_line_before_cursor
        ri = line.rfind(' ')
        ri = ri if ri >= 0 else 0
        word = line[ri:]
        for macro in self.macros:
            if macro[:len(word)] == word:
                yield Completion(macro, start_position = ri - len(line))

history = InMemoryHistory()

macros = {}
def run_text(text, w):
    if len(text.strip()) == 0 or text[0] == ';':
        return [], w

    lines = []
    if text[0] == '!':
        if text == '!dump':
            lines.append(w)

        if text == '!continue':
            w.normalize()
            if w.normal_form:
                lines.append(w)
            else:
                lines.append('Stopped after 5000 reductions. You can !continue ' +
                'for another 5000 iterations or !dump intermediate results.')

        if text[:4] == '!let':
            text = text[5:]
            symbol = text[:text.index(' ')]
            expr = text[text.index(' ') + 1:]

            nmap = WrapNmap()
            w = wrapify(parse(tokenize(expr)), nmap.root)
            unbound = nmap.unbound_map.keys() - macros.keys()
            if len(unbound) > 0:
                lines.append('Warning: the following symbols are unbound: %s' % (', ').join(unbound))
                lines.append('Proceeding with unbound symbols.')
            for m, v in macros.items():
                if m in nmap.unbound_map:
                    w = w.bind(nmap.name(m), v)
            macros[symbol] = w

        if text[:4] == '!see':
            text = text[4:]
            symbol = text[:text.index(' ')]
            expr = text[text.index(' ') + 1:]

            nmap = WrapNmap()
            w = wrapify(parse(tokenize(expr)), nmap.root)
            unbound = nmap.unbound_map.keys() - macros.keys()
            if len(unbound) > 0:
                lines.append('Warning: the following symbols are unbound: %s' % (', ').join(unbound))
                lines.append('Proceeding with unbound symbols.')
            for m, v in macros.items():
                if m in nmap.unbound_map:
                    w = w.bind(nmap.name(m), v)
            lines.append(w)

        if text[:5] ==  '!gopt':
            lines.append(global_optimism_parameter)

        return lines, w

    nmap = WrapNmap()
    w = wrapify(parse(tokenize(text)), nmap.root)
    unbound = nmap.unbound_map.keys() - macros.keys()
    if len(unbound) > 0:
        lines.append('Warning: the following symbols are unbound: %s' % (', ').join(unbound))
        lines.append('Proceeding with unbound symbols.')
    for m, v in macros.items():
        if m in nmap.unbound_map:
            w = w.bind(nmap.name(m), v)
    w.normalize()
    if w.normal_form:
        lines.append(w)
    else:
        lines.append('Stopped after 5000 reductions. You can !continue ' +
            'for another 5000 iterations or !dump intermediate results.')
    return lines, w

for fname in sys.argv[1:]:
    with open(fname) as f:
        lines = []
        current_line = ''
        for line in f:
            if line[0] in '!;':
                lines.append(current_line)
                current_line = line
            else:
                current_line += line
        lines = lines[1:]
        lines.append(current_line)

        for line in lines:
            for p in run_text(line, None)[0]:
                print(p)

w = None
while True:
    text = prompt('(church) ',
            history = history,
            auto_suggest = AutoSuggestFromHistory(),
            completer = MacroCompleter(macros)
    )
    try:
        p, w = run_text(text, w)
        for line in p:
            print(line)
    except Exception as e:
        print(e)
