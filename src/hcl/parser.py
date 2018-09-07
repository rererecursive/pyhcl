
from os.path import abspath, dirname, exists, join
from enum import Enum
import re, sys

from lexer import Lexer
from ply import lex, yacc
import util

import inspect

DEBUG = False
ERROR_STATE = None

# When using something like pyinstaller, the __file__ attribute isn't actually
# set correctly, so the parse file isn't able to be saved anywhere sensible.
# In these cases, just use a temporary directory, it doesn't take too long to
# generate the tables anyways...

if exists(dirname(__file__)):
    pickle_file = abspath(join(dirname(__file__), 'parsetab.dat'))
else:
    import tempfile
    fobj = tempfile.NamedTemporaryFile()
    pickle_file = fobj.name


if sys.version_info[0] < 3:
    def iteritems(d):
        return iter(d.iteritems())
else:
    def iteritems(d):
        return iter(d.items())


class HclParser(object):

    #
    # Tokens
    #

    tokens = (
        'BOOL',
        'FLOAT',
        'NUMBER',
        'COMMA', 'COMMAEND', 'IDENTIFIER', 'EQUAL', 'STRING', 'MINUS',
        'LEFTBRACE', 'RIGHTBRACE', 'LEFTBRACKET', 'RIGHTBRACKET', 'PERIOD',
        'EPLUS', 'EMINUS', 'NEWLINE'
    )

    #
    # Yacc parser section
    #
    def objectlist_flat(self, lt, replace):
        '''
            Similar to the dict constructor, but handles dups

            HCL is unclear on what one should do when duplicate keys are
            encountered. These comments aren't clear either:

            from decoder.go: if we're at the root or we're directly within
                             a list, decode into dicts, otherwise lists

            from object.go: there's a flattened list structure
        '''
        d = {}

        for k,v in lt:
            if k in d.keys() and not replace:
                if type(d[k]) is list:
                    d[k].append(v)
                else:
                    d[k] = [d[k],v]
            else:
                if isinstance(v, dict):
                    dd = d.setdefault(k, {})
                    for kk, vv in iteritems(v):
                        if type(dd) == list:
                            dd.append({kk: vv})
                        elif kk in dd.keys():
                            if hasattr(vv, 'items'):
                                for k2, v2 in iteritems(vv):
                                    dd[kk][k2] = v2
                            else:
                                d[k] = [dd, {kk: vv}]
                        else:
                            dd[kk] = vv
                else:
                    d[k] = v

        return d

    def p_top(self, p):
        "top : objectlist"
        if DEBUG:
            self.print_p(p)
        p[0] = self.objectlist_flat(p[1],True)


    def p_objectlist_0(self, p):
        "objectlist : objectitem"
        if DEBUG:
            self.print_p(p)
        if not p[1]:
            return
        p[0] = [p[1]]

    def p_objectlist_1(self, p):
        "objectlist : objectlist objectitem"
        if DEBUG:
            self.print_p(p)
        if not p[1]:
            p[0] = [p[2]]
        elif not p[2]:
            p[0] = p[1]
        else:
            p[0] = p[1] + [p[2]]
        if DEBUG:
            self.print_p(p)

    def p_objectlist_2(self, p):
        "objectlist : objectlist COMMA objectitem"
        if DEBUG:
            self.print_p(p)
        p[0] = p[1] + [p[3]]

    def p_object_0(self, p):
        "object : LEFTBRACE objectlist RIGHTBRACE"
        if DEBUG:
            self.print_p(p)
        p[0] = self.objectlist_flat(p[2],False)

    def p_object_1(self, p):
        "object : LEFTBRACE objectlist COMMA RIGHTBRACE"
        if DEBUG:
            self.print_p(p)
        p[0] = self.objectlist_flat(p[2],False)

    def p_object_2(self, p):
        "object : LEFTBRACE RIGHTBRACE"
        if DEBUG:
            self.print_p(p)
        p[0] = {}

    def p_objectkey_0(self, p):
        '''
        objectkey : IDENTIFIER
                  | STRING
        '''
        if DEBUG:
            self.print_p(p)
        p[0] = p[1]

    def p_objectitem_0(self, p):
        '''
        objectitem : objectkey EQUAL number
                   | objectkey EQUAL BOOL
                   | objectkey EQUAL STRING
                   | objectkey EQUAL object
                   | objectkey EQUAL list
        '''
        line_no = p.lexer.lex.lineno - 2
        block = self.working_block_stack[-1]
        block.add_argument_item(key=p[1], value=p[3], line_no=line_no)

        if DEBUG:
            self.print_p(p)
        p[0] = (p[1], p[3])

    def p_objectitem_1(self, p):
        "objectitem : NEWLINE"
        # The line number is appended to the token.
        line_no = int(p[1].replace('!NL!', ''))

        try:
            block = self.working_block_stack[-1]
            block.blank_lines.append(line_no)
        except IndexError:
            # We're not inside a block.
            self.top.blank_lines.append(line_no)

    def p_objectitem_2(self, p):
        "objectitem : block"
        if DEBUG:
            self.print_p(p)
        p[0] = p[1]


    def p_block_0(self, p):
        "block : blockId object"
        # The end of a block.
        line_no = p.lexer.lex.lineno - 2
        block = self.working_block_stack.pop()
        print("DEBUG: Popped block '%s' at line %d." % (block, line_no))
        block.line_end = line_no

        try:
            self.working_block_stack[-1].add_argument_block(block)
        except IndexError:
            self.top.blocks.append(block)

        if DEBUG:
            self.print_p(p)
        p[0] = (p[1], p[2])

    def p_block_1(self, p):
        "block : blockId block"
        if DEBUG:
            self.print_p(p)
        p[0] = (p[1], {p[2][0]: p[2][1]})

    def p_blockId(self, p):
        '''
        blockId : IDENTIFIER
                | STRING
        '''
        # The beginning of a block (i.e. a block definition).
        line_no = p.lexer.lex.lineno - 1
        line_text = p.lexer.input_lines[line_no]
        print("DEBUG: Found block '%s' at line %d." % (line_text, line_no))

        try:
            block = self.working_block_stack[-1]
        except IndexError:
            self.working_block_stack.append(Block(line_start=line_no))
            block = self.working_block_stack[-1]

        if block.line_start != line_no:
            # A new block.
            print("DEBUG: Found nested block '%s' at line %d." % (line_text, line_no))
            new_block = Block(line_start=line_no)
            new_block.add_definition_item(p[1], line_text)
            self.working_block_stack.append(new_block)
        else:
            block.add_definition_item(p[1], line_text)

        if DEBUG:
            self.print_p(p)
        p[0] = p[1]


    def p_list_0(self, p):
        '''
        list : LEFTBRACKET listitems RIGHTBRACKET
             | LEFTBRACKET listitems COMMA RIGHTBRACKET
        '''
        if DEBUG:
            self.print_p(p)
        p[0] = p[2]

    def p_list_1(self, p):
        "list : LEFTBRACKET RIGHTBRACKET"
        if DEBUG:
            self.print_p(p)
        p[0] = []


    def p_listitems_0(self, p):
        "listitems : listitem"
        if DEBUG:
            self.print_p(p)
        p[0] = [p[1]]

    def p_listitems_1(self, p):
        "listitems : listitems COMMA listitem"
        if DEBUG:
            self.print_p(p)
        p[0] = p[1] + [p[3]]

    def p_listitem(self, p):
        '''
        listitem : number
                 | object
                 | STRING
        '''
        if DEBUG:
            self.print_p(p)
        p[0] = p[1]

    def p_number_0(self, p):
        "number : int"
        if DEBUG:
            self.print_p(p)
        p[0] = p[1]

    def p_number_1(self, p):
        "number : float"
        if DEBUG:
            self.print_p(p)
        p[0] = float(p[1])

    def p_number_2(self, p):
        "number : int exp"
        if DEBUG:
            self.print_p(p)
        p[0] = float("{0}{1}".format(p[1], p[2]))

    def p_number_3(self, p):
        "number : float exp"
        if DEBUG:
            self.print_p(p)
        p[0] = float("{0}{1}".format(p[1], p[2]))

    def p_int_0(self, p):
        "int : MINUS int"
        if DEBUG:
            self.print_p(p)
        p[0] = -p[2]

    def p_int_1(self, p):
        "int : NUMBER"
        if DEBUG:
            self.print_p(p)
        p[0] = p[1]

    def p_float_0(self, p):
        "float : MINUS float"
        p[0] = p[2] * -1

    def p_float_1(self, p):
        "float : FLOAT"
        p[0] = p[1]

    def p_exp_0(self, p):
        "exp : EPLUS NUMBER"
        if DEBUG:
            self.print_p(p)
        p[0] = "e{0}".format(p[2])

    def p_exp_1(self, p):
        "exp : EMINUS NUMBER"
        if DEBUG:
            self.print_p(p)
        p[0] = "e-{0}".format(p[2])


    # useful for debugging the parser
    def print_p(self, p):
        if DEBUG:
            name = inspect.getouterframes(inspect.currentframe(), 2)[1][3]
            print('(%d) %20s: %s' % (p.lexer.lex.lineno, name, ' | '.join([str(p[i]) for i in range(0, len(p))])))

    def p_error(self, p):
        # Derived from https://groups.google.com/forum/#!topic/ply-hack/spqwuM1Q6gM

        #Ugly hack since Ply doesn't provide any useful error information
        try:
            frame = inspect.currentframe()
            cvars = frame.f_back.f_locals
            expected = "; expected %s" % (', '.join(cvars['actions'][cvars['state']].keys()))
        except:
            expected = ""

        if p is not None:
            msg = "Line %d, column %d: unexpected %s%s" % (p.lineno, p.lexpos, p.type, expected)
        else:
            msg = "Unexpected end of file%s" % expected

        raise ValueError(msg)


    def __init__(self):
        self.yacc = yacc.yacc(module=self, debug=False, optimize=1, picklefile=pickle_file)
        self.lexer = Lexer()

        self.top = Top()
        self.working_block_stack = [] # For calculations


    def parse(self, s):
        lines = s.split('\n')

        # Convert each blank line to !NL!
        for i, line in enumerate(lines):
            if not line.strip():
                # Append the line number as the parser doesn't always know which line it's on
                lines[i] = '!NL!' + str(i)
        s = '\n'.join(lines)

        parsed = self.yacc.parse(s, self.lexer)
        self.top.commented_lines = self.lexer.commented_lines

        return self.top


class Top():
    """Holds all the information about a parsed Terraform file.
    """
    def __init__(self):
        self.blank_lines = []
        self.commented_lines = []
        self.blocks = []

    def to_dictionary(self):
        return util.to_dictionary(self)

class Block():
    """Represents a resource/provider/etc block.
    """
    def __init__(self, line_start=-1):
        self.line_start = line_start
        self.line_end = -1
        self.blank_lines = []
        self.definition = Definition()
        self.arguments = Arguments()

    def add_argument_item(self, key, value, line_no):
        self.arguments.items.append({key: value, 'line_no': line_no})

    def add_argument_block(self, block):
        self.arguments.blocks.append(block)

    def add_definition_item(self, text, line_text):
        index = self.definition.count_instances_of_string(text)
        start = self.find_nth(text, line_text, index)
        end = start + len(text)
        self.definition.add_item(text, start, end)

    def find_nth(self, needle, haystack, n):
        """Find the position of the nth occurrence of a string in another string.
        """
        start = haystack.find(needle)

        while start >= 0 and n > 0:
            start = haystack.find(needle, start+len(needle))
            n -= 1

        return start

class Definition():
    """Represents the definition of a block, e.g. 'resource "aws_instance" "hello"'
    """
    def __init__(self):
        self.keyword = {}
        self.type = {}
        self.name = {}

    def add_item(self, text, start, end):
        """For a definition of length 2, only use the keyword and name.
        For anything longer, include the type.
        """
        if not self.keyword:
            self.keyword = Token(text, start, end)
        elif not self.name:
            self.name = Token(text, start, end)
        else:
            if not self.type:
                self.type = self.name
                self.name = Token(text, start, end)
            else:
                if DEBUG:
                    print ("ERROR: a block cannot have a definition of greater than 3 strings. Skipping...")
                    # TODO: set error status and raise exception

    def count_instances_of_string(self, string):
        """Count the number of times a string appears in the definition.

        Useful for knowing which part of the definition a string is in, as we
        cannot know from the grammar.
        """
        total = 0

        if self.keyword:
            total += self.keyword.text.count(string)
            if self.name:
                total += self.name.text.count(string)
            if self.type:
                total += self.type.text.count(string)

        return total

class Arguments():
    """Represents an argument in a block.
    """
    def __init__(self):
        self.blocks = []
        self.items = []

class Token():
    """Represents a string in a Terraform file.
    """
    def __init__(self, text, start, end):
        self.text = text
        self.start = start
        self.end = end

class Errors(Enum):
    KEEP_PREVIOUS_STATE = 1

