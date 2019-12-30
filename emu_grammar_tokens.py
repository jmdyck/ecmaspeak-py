
# ecmaspeak-py/emu_grammar_tokens.py:
# A bunch of named tuples for representing the symbols etc of an <emu-grammar>.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import textwrap

def mynamedtuple(typename, xfield_names):
    '''
    The essential difference between this function and the built-in namedtuple()
    is that, with this function, the eventual tuples include a field (named 'T')
    whose value is the name of the type.
    From an information POV, this extra field is redundant, but it's useful when
    tuples of different (non-homogeneous) types need to be compared (e.g. for sorting).
    When python compares two tuples, it goes from left to right, looking for a mismatch.
    If we put the T field at the left end, then differently-typed tuples will immediately
    mismatch, thus preventing python from attempting to compare two incomparable fields.

    I copy some code from https://code.activestate.com/recipes/500261/
    or /usr/lib/python3.2/collections.py
    '''
    xfield_names = xfield_names.split()
    afield_names = ['T'] + xfield_names

    _class_template = textwrap.dedent('''
        from operator import itemgetter

        class {typename}(tuple):
            __slots__ = ()

            def __new__(_cls, {arg_list}):
                return tuple.__new__(_cls, ('{typename}', {arg_list}))

            def __repr__(self):
                return '%s({xfields_repr_fmt})' % self

            def items(self):
                {afields_yields}
    \n''')
    class_definition = _class_template.format(
        typename = typename,
        arg_list = ','.join(xfield_names),
        xfields_repr_fmt = ', '.join('{name}=%r'.format(name=field_name) for field_name in xfield_names),
        afields_yields = '; '.join('yield ("%s", self.%s)' % (field_name, field_name) for field_name in afield_names)
    )

    for (i, afield_name) in enumerate(afield_names):
        class_definition += '    %s = property(itemgetter(%d))\n' % (afield_name, i)

    namespace = dict(__name__='namedtuple_%s' % typename)
    try:
        exec(class_definition, namespace)
    except SyntaxError as e:
        raise SyntaxError(e.msg + ':\n\n' + class_definition)
    result = namespace[typename]

    return result

# ------------------------------------------------------------------------------

# I use very short names here so that when a tokenized RHS is printed, it isn't too long.
# Maybe I'll change my mind about that.
GNT           = mynamedtuple('GNT', 'n a o')   # generalized non-terminal
SNT           = mynamedtuple('SNT', 'n')       # simple non-terminal 
T_lit         = mynamedtuple('T_lit', 'c')     # literal characters
T_nc          = mynamedtuple('T_nc', 'n')      # named character
T_u_p         = mynamedtuple('T_u_p', 'p')     # Unicode code point with a Unicode property
T_named       = mynamedtuple('T_named', 'n')   # named terminal
A_guard       = mynamedtuple('A_guard', 's n')
A_id          = mynamedtuple('A_id', 'i')
A_but_only_if = mynamedtuple('A_but_only_if', 'c')
A_but_not     = mynamedtuple('A_but_not', 'b')
A_empty       = mynamedtuple('A_empty', '')
A_no_LT       = mynamedtuple('A_no_LT', '')
LAI           = mynamedtuple('LAI', 'ts')  # lookahead inclusion
LAX           = mynamedtuple('LAX', 'ts')  # lookahead exclusion
Arg           = mynamedtuple('Arg', 's n')
