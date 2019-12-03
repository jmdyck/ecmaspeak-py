
# ecmaspeak-py/shared.py:
# Various things shared betwen modules, mainly the 'spec' object.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, os, re, pickle, pdb

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

g_outdir = None

def register_output_dir(outdir):
    global g_outdir
    g_outdir = outdir

def open_for_output(base):
    if not os.path.exists(g_outdir):
        os.mkdir(g_outdir)
    path = os.path.join(g_outdir, base + '.new')
    return open(path, 'w', encoding='utf-8')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class _Spec:

    def read_source_file(self, source_filepath):
        stderr("reading spec...")
        self.text = open(source_filepath,'r', encoding='utf-8').read()

        # XXX figure these out later:
        # if which == '-render':
        #     self.text = expand_imports(self.text)
        # if os.getcwd().endswith('/proposal-bigint'):
        #     self.text = handle_insdel(self.text)
        #     open('_master/spec_sans_insdel.html.new', 'w').write(self.text)

        install_spec_text(self.text)

    def save(self):
        stderr('pickling...')
        with open(g_outdir + '/spec.pickle','wb') as fp:
            pickle.dump(self, fp)

    def restore(self):
        stderr('unpickling...')
        with open(g_outdir + '/spec.pickle', 'rb') as fp:
            spec = pickle.load(fp)
        self.__dict__.update(spec.__dict__)
        # spec_text = open('spec.html','r', encoding='utf-8').read()
        install_spec_text(self.text)

spec = _Spec()

def install_spec_text(_spec_text):
    global spec_text, _newline_posns
    spec_text = _spec_text

    _newline_posns = [-1] + [mo.start() for mo in re.finditer('\n', spec_text)]
    # _newline_posn[i] is the (0-based) position within spec_text
    # of the newline character that ends line i (1-based).
    # (And we pretend that there's a line 0
    # that ends with a newline at position -1.)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

spec_text = None
_newline_posns = None

def convert_HTMLParser_getpos_to_posn(pos_tuple):
    (line_num, offset_within_line) = pos_tuple
    return _newline_posns[line_num-1] + 1 + offset_within_line

def convert_posn_to_linecol(posn):

    # bisection
    lo = 0
    hi = len(_newline_posns) - 1
    while True:
        assert lo < hi
        assert _newline_posns[lo] < posn <= _newline_posns[hi]
        if lo + 1 == hi:
            line_num = hi
            col = posn - _newline_posns[lo]
            break

        mid = (lo + hi) // 2
        assert lo < mid < hi
        mid_posn = _newline_posns[mid]
        if mid_posn < posn:
            lo = mid
        elif posn < mid_posn:
            hi = mid
        else:
            # direct hit
            assert spec_text[posn] == '\n'
            # Associate it with the preceding line.
            lo = mid - 1
            hi = mid

    return (line_num, col)

def source_line_with_caret_marking_column(posn):
    (line_num, col_num) = convert_posn_to_linecol(posn)
    source_line = spec_text[
        _newline_posns[line_num-1]+1
        :
        _newline_posns[line_num]
    ]
    caret_line = '-' * (col_num-1) + '^'

    return source_line + '\n' + caret_line

g_warnings_f = None

def msg_at_posn(posn, msg):
    (line_num, col_num) = convert_posn_to_linecol(posn)
    print("line %5d, col %3d: %s" % (line_num, col_num, msg), file=g_warnings_f)

def header(msg):
    print("\n" + msg + "\n", file=g_warnings_f)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# We *don't* mutate the HTML tree and then serialize it.
# Instead, we write the spec_text with replacements.
# Each replacement is a tuple:
# (start_posn, end_posn, replacement_string)

def write_spec_with_replacements(base, replacements):
    f = open_for_output(base)
    def put(*s): print(*s, end='', file=f)

    replacements.sort()

    prev_posn = 0
    for (r_start_posn, r_end_posn, replacement_string) in replacements:
        assert prev_posn <= r_start_posn
        # I.e., we require that the replaced chunks be non-overlapping.
        put(spec_text[prev_posn:r_start_posn])
        put(replacement_string)
        prev_posn = r_end_posn
    put(spec_text[prev_posn:])

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class rem: # re with a memory

    def _init__(self):
        self.mo = None

    def fullmatch(self, pattern, subject):
        self.mo = re.fullmatch(pattern, subject)
        return self.mo

    def group(self, i):
        assert self.mo
        return self.mo.group(i)

    def groups(self):
        assert self.mo
        return self.mo.groups()

RE = rem()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def stderr(*s, **kwargs):
    print(*s, **kwargs, file=sys.stderr)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
