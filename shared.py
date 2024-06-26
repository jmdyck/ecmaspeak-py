
# ecmaspeak-py/shared.py:
# Various things shared betwen modules, mainly the 'spec' object.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, os, re, pickle, pdb, collections

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
        pickle_file = g_outdir + '/spec.pickle'
        stderr(f'pickling {pickle_file} ...')
        with open(pickle_file,'wb') as fp:
            pickle.dump(self, fp)

    def restore(self):
        pickle_file = g_outdir + '/spec.pickle'
        stderr(f'unpickling {pickle_file} ...')
        with open(pickle_file, 'rb') as fp:
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

class SpecNode:
    def __init__(self, start_posn, end_posn):
        assert start_posn is not None
        # but end_posn might be None
        self.start_posn = start_posn
        self.end_posn = end_posn
        self.children = []

    # ------------------------------------

    def source_text(self):
        assert self.end_posn is not None
        return spec_text[self.start_posn:self.end_posn]

    # ------------------------------------

    def preorder_traversal(self, visit):
        r = visit(self)
        if r is None:
            pass
        elif r == 'prune':
            return
        else:
            assert 0, r

        for child in self.children:
            child.preorder_traversal(visit)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def print_tree(root, prefix, f):
    # Assumes every descendant of {root} has attributes `children` and `tree_slug`

    def recurse(node, prefix, self_is_last_child):

        if self_is_last_child:
            bit_for_first_line  = "'-"
            bit_for_later_lines = '  '
            # bit_for_first_line = '\u2517'
            # bit_for_later_lines = ' '
        else:
            bit_for_first_line  = '|-'
            bit_for_later_lines = '| '
            # bit_for_first_line = '\u2523'
            # bit_for_later_lines = '\u2503'

        if node is None:
            print(prefix + bit_for_first_line + ' ' + '(nothing)', file=f)
            return

        print(prefix + bit_for_first_line + ' ' + node.tree_slug(), file=f)

        n_children = len(node.children)
        if n_children > 0:
            child_prefix = prefix + bit_for_later_lines + ' '
            for (i,child) in enumerate(node.children):
                recurse(child, child_prefix, (i == n_children-1))

        if hasattr(node, 'covered_thing'):
            print(prefix + bit_for_later_lines + 'COVERS', file=f)
            covered_prefix = prefix + bit_for_later_lines + ' '
            recurse(node.covered_thing, covered_prefix, True)

    recurse(root, prefix, True)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# This isn't a good abstraction yet.

class LineInfo:
    def __init__(self, line_num, start_posn, end_posn, indentation):
        self.line_num = line_num
        self.start_posn = start_posn
        self.end_posn = end_posn
        self.indentation = indentation
        self.suppress = False
        self.afters = []
        self.targeted_msgs = []

def prep_for_line_info():
    stderr('prep_for_line_info ...')
    ln = 0
    spec.info_for_line_ = [None] # "line #0"
    for mo in re.finditer('(?m)^( *).*$', spec.text):
        (s,e) = mo.span()

        # If `spec.text` ends with a newline,
        # then the pattern will match immediately after that newline,
        # but we don't want a line for that.
        if s == e and s == len(spec.text):
            break

        i = len(mo.group(1))
        ln += 1
        spec.info_for_line_.append(LineInfo(ln, s, e, i))

def put_targeted_msg(anode, msg):
    # We *could* just attach {msg} to {anode},
    # but then at each line, we'd need to get all the nodes
    # that pertain to that line (i.e., end on it),
    # and that'd be a pain?

    (sl, sc) = convert_posn_to_linecol(anode.start_posn)
    (el, ec) = convert_posn_to_linecol(anode.end_posn)
    if sl == el:
        thing = (sc, ec, msg)
    else:
        stderr("Node spans multiple lines: (%d,%d) to (%d,%d)" % (sl,sc,el,ec))
        thing = (0, ec, msg)
    spec.info_for_line_[el].targeted_msgs.append(thing)

def write_spec_with_extras(mode, show_targeted_msgs, f):
    for line_info in spec.info_for_line_[1:]:

        if not line_info.suppress:
            print(spec.text[line_info.start_posn:line_info.end_posn], file=f)

        if line_info.afters:
            indentation = line_info.indentation
            if indentation == 0:
                # somewhat kludgey
                indentation = spec.info_for_line_[line_info.line_num-1].indentation

            for after_thing in line_info.afters:
                for line in after_thing.lines(indentation, mode):
                    print(line, file=f)

        if show_targeted_msgs:
            # For each anode that ends on this line,
            # show any messages relating to that anode.

            # For things on the same line, secondary sort by *end*-column.
            for (sc,ec,msg) in sorted(line_info.targeted_msgs, key=lambda t: t[1]):
                caret_line = '-' * (sc-1) + '^' * (ec-sc)
                print(caret_line, file=f)
                for line in msg.split('\n'):
                    print('>>> ' + line, file=f)
                print(file=f)

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

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# a file containing a copy of spec.html, with each message under its relevant line

msgs_for_line_ = None

def msg_at_posn_start():
    global msgs_for_line_
    msgs_for_line_ = collections.defaultdict(list)

def msg_at_node(node, msg):
    msg_at_posn(node.start_posn, msg)

def msg_at_posn(posn, msg):
    (line_num, col_num) = convert_posn_to_linecol(posn)
    msgs_for_line_[line_num].append((col_num, msg))

def msg_at_posn_finish():
    f = open_for_output('msgs_in_spec.html')
    for (line_i, line) in enumerate(spec_text.split('\n')):
        print(line, file=f)
        line_num = line_i + 1
        for (col, msg) in sorted(msgs_for_line_[line_num]):
            print('-' * (col-1) + '^', file=f)
            print('--', msg, file=f)
    f.close()

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

class DL:
    # A utility for creating <dl> elements
    # (of the particular kind that static_type_analysis generates).

    def __init__(self, indentation):
        self.indentation = indentation
        self.lines = []
        self.expecting = '<dl>'

    def start(self):
        assert self.expecting == '<dl>'
        self._pwi(f"<dl class='header'>")
        self.expecting = '<dt>'

    def dt(self, dt_content):
        assert self.expecting == '<dt>'
        self._pwi('')
        self._pwi(f"  <dt>{dt_content}</dt>")
        self.expecting = '<dd>'

    def dd(self, dd_content):
        assert self.expecting == '<dd>'
        self._pwi(f"  <dd>{dd_content}</dd>")
        self.expecting = '<dt>'

    def dd_ul_start(self, lefts):
        assert self.expecting == '<dd>'
        self._pwi(f"  <dd>")
        self._pwi(f"    <ul>")
        self.expecting = '<li>'
        self.left_max_width = max(len(left) for left in lefts)

    def dd_ul_li(self, left, right):
        assert self.expecting == '<li>'
        padded_left = left.ljust(self.left_max_width)
        self._pwi(f"      <li>{padded_left} : {right}</li>")
        self.latest_right_len = len(right)

    def dd_ul_li_comment(self, msg):
        assert self.expecting == '<li>'
        # We assume it's always a comment on the 'right' part.
        lead_up = self.indentation + 6 + 4 + self.left_max_width + 3
        # 6 for extra indentation, 4 for "<li>", 3 for " : "
        self.lines.append('-' * lead_up + '^' * self.latest_right_len)
        self.lines.append('>>> ' + msg)
        self.lines.append('')

    def dd_ul_end(self):
        assert self.expecting == '<li>'
        self._pwi(f"    </ul>")
        self._pwi(f"  </dd>")
        self.expecting = '<dt>'

    def end(self):
        assert self.expecting == '<dt>'
        self._pwi(f"</dl>")
        self.expecting = None
        return self.lines

    def _pwi(self, s): # put-with-indentation
        ind_str = ' ' * self.indentation
        self.lines.append('' if s == '' else ind_str + s)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def decode_entities(text):
    assert '<' not in text, text
    # assert '>' not in text 
    # comment it out due to "[>" in grammars?
    return ( text
        .replace(r'&lt;', '<')
        .replace(r'&gt;', '>')
        .replace(r'&ldquo;', '\u201C')
        .replace(r'&rdquo;', '\u201D')
        .replace(r'&amp;', '&')
    )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def stderr(*s, **kwargs):
    print(*s, **kwargs, file=sys.stderr)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
