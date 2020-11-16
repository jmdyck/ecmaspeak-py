
# ecmaspeak-py/mynamedtuple.py:
# A variant of collections.namedtuple
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import textwrap

def mynamedtuple(typename, xfield_names):
    '''
    The essential difference between this function and the built-in namedtuple()
    is that, with this function, the eventual tuples include an initial field (named 'T')
    whose value is the name of the type.
    From an information POV, this extra field is redundant, but it's useful when
    tuples of different (non-homogeneous) types need to be compared (e.g., for sorting).
    When python compares two tuples, it goes from left to right, looking for a mismatch;
    but if it encounters two fields with incomparable values
    (e.g., a string and a bool), it raises an exception.
    By putting the T field at the left end of each tuple,
    differently-typed tuples will immediately mismatch,
    preventing python from attempting to compare two incomparable values.

    (Also, with collections.namedtuple, two instances of different types
    will compare equal if their corresponding field-values are equal,
    which is often not wanted.
    With mynamedtuple, two values of different types will never compare equal.)

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
