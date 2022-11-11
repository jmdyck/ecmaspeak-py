
# ecmaspeak-py/HTML.py:
# Parse and validate ecmarkup's flavor of HTML.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re
from html.parser import HTMLParser
from collections import OrderedDict

import shared
from shared import stderr, msg_at_posn, SpecNode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_and_validate():
    doc_node = _parse()
    if doc_node.element_name != '#DOC':
        stderr("After _parse(), doc_node.element_name should be #DOC, is", doc_node.element_name)
        stderr("start_posn ~", shared.convert_posn_to_linecol(doc_node.start_posn))
        stderr("aborting due to above error")
        sys.exit()
    _validate(doc_node)
    return doc_node

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _parse():
    stderr("parsing spec...")

    doc_node = HNode(0, len(shared.spec_text), '#DOC', {})
    doc_node.parent = None
    current_open_node = doc_node

    def add_child(child):
        nonlocal current_open_node
        current_open_node.children.append(child)
        child.parent = current_open_node
        if child.element_name.startswith('#') or child.element_name in ['html', 'meta', 'link', 'img', 'br']:
            # This is a complete child
            pass
        else:
            # This is an incomplete ("open") element.
            # (It should be closed eventually by a corresponding end-tag.)
            current_open_node = child

    def close_open_child(end_tag_start_posn, end_tag_end_posn, element_name):
        nonlocal current_open_node
        if element_name != current_open_node.element_name:
            msg_at_posn(
                end_tag_start_posn,
                f"ERROR: The currently-open element is a {current_open_node.element_name!r}, but this is an end-tag for {element_name!r}.\nSkipping the end-tag, to see if that helps."

            )
            # This old code might be useful to adapt:
            # if current_open_node.parent is None:
            #     self._report("current_open_node.parent is None")
            # elif element_name == current_open_node.parent.element_name:
            #     self._report("Assuming that </%s> is missing" % current_open_node.element_name)
            #     # Pretend that we got the missing endtag:
            #     self.handle_endtag(current_open_node.element_name)
            #     # That will change current_open_node.
            #     assert element_name == current_open_node.element_name
            #     self.handle_endtag(current_open_node.element_name)
            return

        current_open_node.inner_start_posn = current_open_node.end_posn
        current_open_node.inner_end_posn   = end_tag_start_posn
        current_open_node.end_posn         = end_tag_end_posn
        current_open_node = current_open_node.parent

    # ---------------------------------------------

    pattern_funcs = []
    def for_pattern(pattern):
        reo = re.compile(pattern)
        def wrapper(f):
            pattern_funcs.append( (reo, f) )
            return None
        return wrapper

    # ---------------------------------------------

    # non-markup text:
    @for_pattern(r'[^<]+')
    def _(start_posn, end_posn, _):
        add_child(HNode(start_posn, end_posn, '#LITERAL', {}))
        return end_posn

    # start-tag:
    @for_pattern(r'<([a-z][-a-z0-9]*)\b')
    def _(tag_start_posn, end_name_posn, groups):
        [element_name] = groups
        attrs = OrderedDict()
        posn = end_name_posn
        while True:
            if shared.spec_text[posn] == '>':
                tag_end_posn = posn + 1
                break
            mo = re.compile(r' ([a-z][-a-z0-9]*)(?:="([^"]*)")?').match(shared.spec_text, posn)
            if mo:
                (attr_name, attr_value) = mo.groups()
                assert attr_name not in attrs
                attrs[attr_name] = attr_value
                posn = mo.end()
                continue

            fatal_error(posn, "lexing error")

        add_child(HNode(tag_start_posn, tag_end_posn, element_name, attrs))
        return tag_end_posn

    # end-tag:
    @for_pattern(r'</([a-z][-a-z0-9]*)>')
    def _(start_posn, end_posn, groups):
        [element_name] = groups
        close_open_child(start_posn, end_posn, element_name)
        return end_posn

    # comment:
    @for_pattern(r'(?s)<!--.*?-->')
    def _(start_posn, end_posn, _):
        add_child(HNode(start_posn, end_posn, '#COMMENT', {}))
        return end_posn

    # doctype-decl:
    @for_pattern(r'<!DOCTYPE html>')
    def _(start_posn, end_posn, _):
        add_child(HNode(start_posn, end_posn, '#DECL', {}))
        return end_posn

    # ---------------------------------------------

    def fatal_error(posn, msg):
        (line_num, col_num) = shared.convert_posn_to_linecol(posn)
        stderr()
        stderr("********************************************")
        stderr(f"line {line_num}, col {col_num}:")
        stderr(repr(shared.spec_text[posn:posn+30] + '...'))
        stderr(msg)
        stderr("********************************************")
        sys.exit(1)

    # ---------------------------------------------

    posn = 0
    while posn < len(shared.spec_text):
        for (reo, func) in pattern_funcs:
            mo = reo.match(shared.spec_text, posn)
            if mo:
                posn = func(mo.start(), mo.end(), mo.groups())
                break
        else:
            fatal_error(posn, "lexing error")

    if current_open_node.element_name != '#DOC':
        msg_at_posn(
            current_open_node.start_posn,
            "ERROR: At end of file, this element is still open"
        )
        fatal_error(current_open_node.start_posn, f"At end of file, this element is still open")

    return doc_node

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class HNode(SpecNode):
    def __init__(self, start_posn, end_posn, element_name, attrs):
        # stderr(start_posn, end_posn, element_name, attrs)
        SpecNode.__init__(self, start_posn, end_posn)
        self.element_name = element_name
        self.attrs = attrs

    def __repr__(self):
        return f"HNode<{self.element_name}>"

    def inner_source_text(self):
        return shared.spec_text[self.inner_start_posn:self.inner_end_posn]

    def is_element(self):
        return not self.element_name.startswith('#')

    def is_textual(self):
        return (self.element_name == '#LITERAL')

    def is_whitespace(self):
        return self.element_name == '#LITERAL' and string_is_whitespace(self.source_text())

    def is_nonwhite_text(self):
        return (
            self.element_name == '#LITERAL'
            and
            not string_is_whitespace(self.source_text())
        )

    def is_a_section(self):
        return self.element_name in ['emu-intro', 'emu-clause', 'emu-annex']

    def each_child_named(self, element_name):
        for child in self.children:
            if hasattr(element_name, 'fullmatch'):
                if element_name.fullmatch(child.element_name):
                    yield child
            else:
                if child.element_name == element_name:
                    yield child

    def each_descendant_named(self, element_name):
        # actually, descendant-or-self
        if hasattr(element_name, 'fullmatch'):
            if element_name.fullmatch(self.element_name):
                yield self
        else:
            if self.element_name == element_name:
                yield self
        for child in self.children:
            for d in child.each_descendant_named(element_name):
                yield d

    def each_descendant_that_is_a_section(self):
        if self.is_a_section():
            yield self
        for child in self.section_children:
            for s in child.each_descendant_that_is_a_section():
                yield s

    def closest_containing_section(self):
        return self.nearest_ancestor_satisfying(lambda node: node.is_a_section())

    def nearest_ancestor_satisfying(self, predicate):
        if predicate(self):
            return self
        elif self.parent is None:
            return None
        else:
            return self.parent.nearest_ancestor_satisfying(predicate)

reo_whitespace = re.compile(r'^\s+$')

def string_is_whitespace(s):
    return (reo_whitespace.match(s) is not None)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def _validate(node):
    if node.element_name == '#DOC':
        stderr("validating markup...")

    def is_loose_about_spaces(x):
        # In   sec-assignment-operators-runtime-semantics-evaluation
        # and  sec-applystringornumericbinaryoperator.
        # we have <emu-alg> elements that contain 'lightweight' tables
        # where we format the source with extra spaces in the <th> and <td> elements
        # to make the source easier to read.
        return (
            x.element_name in ['th', 'td']
            and
            x.parent.parent.attrs.get('class', None) == 'lightweight-table'
            # x.parent is the <tr>
            # x.parent.parent is the <table>
        )
        # TODO: Base it on the presence of "<!-- emu-format ignore -->",
        # because not all lightweight-tables are loose about spaces.

    if node.element_name == '#LITERAL':
        # Check for runs of multiple space characters.
        for mo in re.compile(r' {2,}').finditer(shared.spec.text, node.start_posn, node.end_posn):
            s_posn = mo.start()
            n_spaces = mo.end() - mo.start()
            if shared.spec.text[s_posn-1] == '\n':
                # indentation
                continue

            if is_loose_about_spaces(node.parent):
                continue

            msg_at_posn(
                s_posn,
                f"{n_spaces} space characters"
            )

        # Check for HTML entities
        allowed_and_disallowed = [
            ('&amp;' , '&'   ),
            ('&lt;'  , '<'   ),
            ('&nbsp;', '\xa0'),
            ('&reg;' , '\xae'),
        ]
        if node.parent.element_name in ['emu-grammar']:
            allowed_and_disallowed.extend([
                ('&gt;'   , None    ), # emu-grammar has both
                ('&ldquo;', '\u201c'),
                ('&rdquo;', '\u201d'),
                ('&isin;' , '\u2208'),
                ('&notin;', '\u2209'),
                ('&le;'   , '\u2264'),
            ])
        if node.parent.element_name in ['h1']:
            allowed_and_disallowed.extend([
                ('&infin;', '\u221e'),
                ('&gt;'   , None    ),
            ])
        if node.parent.element_name in ['code', 'td']:
            allowed_and_disallowed.extend([
                ('&gt;'    , None    ),
                ('&hellip;', '\u2026'),
                ('&#x0307;', '\u0307'),
                ('&#x030A;', '\u030A'),
                ('&#x0323;', '\u0323'),
                ('&#x03A9;', '\u03A9'),
                ('&#x1100;', '\u1100'),
                ('&#x1161;', '\u1161'),
                ('&#x1E0B;', '\u1E0B'),
                ('&#x1E0D;', '\u1E0D'),
                ('&#x1E69;', '\u1E69'),
                ('&#x2126;', '\u2126'),
                ('&#x212B;', '\u212B'),
                ('&#xAC00;', '\uAC00'),
            ])

        allowed_entities = []
        disallowed_characters = []
        for (entity_text, character) in allowed_and_disallowed:
            allowed_entities.append(entity_text)
            if character is not None:
                disallowed_characters.append(character)

        for mo in re.compile(r'&#?\w+;|.').finditer(shared.spec.text, node.start_posn, node.end_posn):
            s_posn = mo.start()
            n_chars = mo.end() - mo.start()
            match_text = mo.group(0)
            assert n_chars > 0
            if n_chars == 1:
                # literal character
                if match_text in disallowed_characters:
                    msg_at_posn(
                        s_posn,
                        f"literal {match_text!r} should be an entity"
                    )
            else:
                # entity
                if match_text not in allowed_entities:
                    msg_at_posn(
                        s_posn,
                        f"entity {match_text!r} should be literal character"
                    )
            continue


        return # because nothing else in this function will apply

    # ------------------------

    if hasattr(node, 'inner_start_posn') and not is_loose_about_spaces(node):
        ist = node.inner_source_text()
        if ist.startswith(' '):
            msg_at_posn(node.inner_start_posn, f"<{node.element_name}> content starts with space")

        if re.search('\n +$', ist):
            # That's just an indented end-tag
            pass
        elif ist.endswith(' '):
            msg_at_posn(node.inner_end_posn, f"<{node.element_name}> content ends with space")


    # ------------------------

    required_attrs = required_attrs_[node.element_name]
    optional_attrs = optional_attrs_[node.element_name]
    attrs = node.attrs.keys()

    def stringify_set(s):
        return ' '.join(sorted(s))

    if not (attrs >= required_attrs):
        msg_at_posn(node.start_posn, f"required attribute(s) are missing: {stringify_set(required_attrs - attrs)}")
    if not (attrs <= required_attrs | optional_attrs):
        msg_at_posn(node.start_posn, f"unexpected attribute(s): {stringify_set(attrs - (required_attrs | optional_attrs))}")

    for (attr_name, attr_value) in node.attrs.items():
        assert attr_value is None or isinstance(attr_value, str)
        for key in [
            f"{node.element_name}.{attr_name}",
            attr_name
        ]:
            if key in attribute_info:
                value_pattern = attribute_info[key]
                break
        else:
            msg_at_posn(
                node.start_posn,
                f"Unknown attribute {attr_name!r}"
            )
            continue

        if value_pattern is None and attr_value is None:
            pass
        elif value_pattern is None:
            msg_at_posn(
                node.start_posn,
                f"For attribute {attr_name!r}, expected no value, but got {attr_value!r}"
            )
        elif attr_value is None:
            msg_at_posn(
                node.start_posn,
                f"For attribute {attr_name!r}, expected a value matching {value_pattern!r}, but got nothing"
            )
        else:
            if not re.fullmatch(value_pattern, attr_value):
                msg_at_posn(
                    node.start_posn,
                    f"For attribute {attr_name!r}, expected a value matching {value_pattern!r}, but got {attr_value!r}"
                )

    # ------------------------

    # First do a pass to figure whether the content of this node
    # is block items or inline items or (anomalously) both.
    node.block_child_element_names = set()
    node.inline_child_element_names = set()
    for child in node.children:
        if child.element_name == '#COMMENT':
            continue
        elif child.element_name == '#LITERAL':
            if not child.is_whitespace():
                node.inline_child_element_names.add(child.element_name)
        elif child.element_name in kind_:
            k = kind_[child.element_name]
            if k == 'B':
                node.block_child_element_names.add(child.element_name)
            elif k == 'I':
                node.inline_child_element_names.add(child.element_name)
        else:
            msg_at_posn(child.start_posn, "Is <%s> block or inline?" % child.element_name)

    if node.block_child_element_names and node.inline_child_element_names:
        msg_at_posn(node.start_posn, "%s content includes both block-level items (%s) and inline-level items (%s)" % (
                node.element_name,
                ', '.join(sorted(list(node.block_child_element_names))),
                ', '.join(sorted(list(node.inline_child_element_names)))
            )
        )

    # ------------------------

    children_names = []
    for child in node.children:
        if child.element_name == '#LITERAL':
            if node.inline_child_element_names:
                x = '#TEXT;'
            else:
                assert child.is_whitespace()
                x = '#WS;'
        else:
            x = child.element_name + ';'
        children_names.append(x)

    children_names = ''.join(children_names)
    children_names = re.sub('#WS;#COMMENT;#WS;', '#WS;', children_names)

    if node.element_name not in content_model_:
        msg_at_posn(node.start_posn, "No content model for <%s>" % node.element_name)
    else:
        content_model = content_model_[node.element_name]
        mo = re.match(content_model, children_names)
        if mo is None:
            msg_at_posn(node.start_posn, "%s has content %s, expected %s" %
                (node.element_name, children_names, content_model))

    #! if node.children:
    #!     node.inner_start_posn = node.children[0].start_posn
    #!     node.inner_end_posn   = node.children[-1].end_posn

    for child in node.children:
        _validate(child)

element_info = {

    # ---------------------------------------------
    # Block-level

        # block contains blocks:
        '#DOC'              : ('B', '',          '',           '#DECL;#WS;html;#WS;meta;#WS;link;#WS;style;#WS;pre;#WS;p;#WS;div;#WS;emu-intro;#WS;(emu-clause;#WS;)+(emu-annex;#WS;)+'),
        'emu-intro'         : ('B', 'id',        '',           '#WS;h1;#WS;((p;|emu-integration-plans;)#WS;)+'),
        'emu-clause'        : ('B', '', 'aoid example id legacy namespace normative-optional oldids type', '#WS;h1;#WS;((div;|dl;|em;|emu-alg;|emu-import;|emu-eqn;|emu-figure;|emu-grammar;|emu-motivation;|emu-note;|emu-table;|figure;|h2;|ol;|p;|pre;|ul;)#WS;)*((emu-clause;|emu-integration-plans;)#WS;)*'),
        'emu-annex'         : ('B', 'id', 'aoid namespace normative oldids type', '#WS;h1;#WS;((dl;|emu-alg;|emu-grammar;|emu-note;|emu-prodref;|emu-table;|h2;|ol;|p;|ul;)#WS;)*(emu-annex;#WS;)*'),
        'emu-table'         : ('B', 'caption id', 'class informative oldids', '#WS;(emu-caption;#WS;)?table;#WS;'),
        'emu-figure'        : ('B', 'caption id', 'informative', '#WS;(object;|img;)#WS;'),
        'figure'            : ('B', '',          '',           '#WS;table;#WS;'),
        'table'             : ('B', '',          'class',      '#WS;(thead;#WS;)?(tr;#WS;)+'),
        'thead'             : ('B', '',          '',           '#WS;(tr;#WS;)+'),
        'tr'                : ('B', '',          '',           '(#WS;)?((th;|td;)(#WS;)?)+'),
        'ul'                : ('B', '',          '',           '#WS;(li;#WS;)+'),
        'ol'                : ('B', '',          '',           '#WS;(li;#WS;)+'),
        'dl'                : ('B', '',          'class',      '#WS;(dt;#WS;dd;#WS;)*'),
        'object'            : ('B', 'data height type width', '',           'img;'),

        # block contains blocks or contains inlines, but not both:
        'emu-integration-plans': ('B', '',          '',           '#WS;(p;#WS;)+|(#TEXT;|a;)+'), # PROPOSALS
        'emu-note'             : ('B', '',          'class id',   '#WS;((div;|emu-alg;|emu-grammar;|emu-table;|figure;|p;|pre;|ul;)#WS;)*|(#TEXT;|a;|emu-not-ref;|emu-xref;|sub;)+'),
        'li'                   : ('B', '',          'oldids',     '#WS;p;#WS;((emu-alg;|emu-note;|ol;|p;|ul;|dl;)#WS;)*|(#COMMENT;|#TEXT;|a;|br;|code;|dfn;|em;|emu-eqn;|emu-grammar;|emu-not-ref;|emu-val;|emu-xref;|i;|ins;|strong;|sub;|sup;|var;)+'), # num-ref: doesn't have to start with TEXT
        'td'                   : ('B', '',          'colspan oldids rowspan', '#WS;((emu-alg;|p;|emu-note;)#WS;)*|(#TEXT;|b;|br;|code;|dfn;|em;|emu-not-ref;|emu-xref;|i;|ins;|sub;|sup;)+'),
        'div'                  : ('B', '',          'class id',   '#WS;((h1;|p;|ul;)#WS;)+|#TEXT;((br;|em;|i;|sup;)#TEXT;)*'),
        'dd'                   : ('B', '',          '',           '#WS;((p;|ul;)#WS;)+|(#TEXT;|a;|code;|dfn;|em;|emu-eqn;|emu-grammar;|emu-xref;|i;|sub;|sup;)+'),

        # block contains inlines:
        'emu-motivation'       : ('B', '',          '',           '(#TEXT;|a;)+'), # PROPOSALS
        'emu-todo'             : ('B', '',          '',           '(#TEXT;|a;)+'), # PROPOSALS
        'emu-alg'              : ('B', '',          'example replaces-step', '(#TEXT;|a;|b;|code;|del;|emu-grammar;|emu-meta;|emu-not-ref;|emu-xref;|figure;|i;|ins;|pre;|sub;|sup;|table;|var;)+'), # BLOCK INCLUSIONS: figure, pre, table
        'emu-caption'          : ('B', '',          '',           '(#TEXT;|emu-xref;)+'),
        'pre'                  : ('B', '',          'class',      '#TEXT;|code;'),
        'style'                : ('B', '',          '',           '#TEXT;'),
        'p'                    : ('B', '',          '',           'img;|(#COMMENT;|#TEXT;|a;|b;|br;|code;|dfn;|em;|emu-eqn;|emu-grammar;|emu-not-ref;|emu-prodref;|emu-t;|emu-xref;|i;|ins;|sub;|sup;|var;)+'), # the img; is just for the logo at the start, weird.
        'h1'                   : ('B', '',          '',           '(#TEXT;|del;|dfn;|emu-xref;|i;|ins;)+'), # though dfn is pretty odd
        'h2'                   : ('B', '',          '',           '#TEXT;'),
        'th'                   : ('B', '',          '',           '#TEXT;(sup;#TEXT;)?'),
        'script'               : ('B', 'src',       '',           '(#TEXT;)?'),
        'dt'                   : ('B', '',          '',           '#TEXT;'),

        # block is empty:
        '#DECL'             : ('B', '',          '',           ''),
        'html'              : ('B', 'lang',      '',           ''),
        'meta'              : ('B', 'charset',   '',           ''),
        'link'              : ('B', 'href rel',  '',           ''),
        'img'               : ('B', 'src',       'alt height id width', ''),
        'emu-import'        : ('B', 'href',      '',           ''),

    # ---------------------------------------------
    # can be block or inline, depending on the context:

        'emu-grammar'       : ('A', '',          'example type', '(#TEXT;|ins;|del;)+'),
        'emu-prodref'       : ('A', 'name',      'a',          ''),
        'emu-eqn'           : ('A', '',          'aoid id',    '#TEXT;(sub;|sup;|#TEXT;)*'),

        'a'                 : ('A', 'href',      '',           '(#TEXT;|code;|del;|ins;)*'),
        # was inline-only, but then BTerlson added <a id='table-9'></a>
        # Could change it back if he accepts oldids edit.

        'em'                : ('A', '',          'id',         '#TEXT;'),
        # was inline-only, but then PR #1062 added
        #    <em>This section is non-normative.</em>
        # as quasi-paragraph.

    # ---------------------------------------------
    # inlines:

        'b'                 : ('I', '',          '',           '(#TEXT;|sub;|sup;)+'),
        'br'                : ('I', '',          '',           ''),
        'code'              : ('I', '',          'class',      '(#TEXT;|i;|var;)+'),
        'del'               : ('I', '',          '',           '(#TEXT;|emu-xref;)+'), # PROPOSALS
        'dfn'               : ('I', '',          'aoid id oldids variants', '(#TEXT;|emu-eqn;)'),
        'emu-meta'          : ('I', '',          'effects suppress-effects', '#TEXT;'),
        'emu-not-ref'       : ('I', '',          '',           '#TEXT;'),
        'emu-t'             : ('I', '',          '',           '#TEXT;'),
        'emu-val'           : ('I', '',          '',           '#TEXT;var;#TEXT;'),
        'emu-xref'          : ('I', 'href',      'title',      '(#TEXT;|code;)?'),
        'i'                 : ('I', '',          '',           '#TEXT;(sup;#TEXT;)?'),
        'ins'               : ('I', '',          '',           '#TEXT;((a;|emu-xref;|sub;)#TEXT;)?'), # PROPOSALS?
        'strong'            : ('I', '',          '',           '(#TEXT;|code;)+'),
        'sub'               : ('I', '',          '',           '#TEXT;|dfn;'), # dfn; for num-ref
        'sup'               : ('I', '',          '',           '(#TEXT;|sub;)+'), # sub; for num-ref
        'var'               : ('I', '',          '',           '#TEXT;'),

    # ---------------------------------------------
    # other:

        '#COMMENT'          : (None, '',          '',           ''),

}

id_pattern = r'[-\w.%@]+'

attribute_info = {
    'pre.class'          : r'metadata',
    'code.class'         : r'javascript|html',
    'dl.class'           : r'header',
    'div.class'          : r'math-display|rhs',
    'table.class'        : r'lightweight-table',
    'emu-table.class'    : r'module-overflow',
    'emu-note.class'     : r'module-overflow-note',

    'object.type'        : r'image/svg\+xml',
    'emu-grammar.type'   : r'definition',
    'emu-clause.type'    : r'abstract operation|concrete method|(host|implementation)-defined abstract operation|internal method|numeric method|sdo',
    'emu-annex.type'     : r'abstract operation',

    'a'                  : r'\w+',
    'alt'                : r'[\w .,()?]+',
    'aoid'               : r'[-\w]+',
    'caption'            : r'[-\w /()<>]+',
    'charset'            : r'utf-8',
    'colspan'            : r'\d',
    'data'               : r'img/figure-1.svg',
    'effects'            : r'user-code',
    'height'             : r'\d+',
    'href'               : r'[-\w:/.#%@]+',
    'id'                 : id_pattern,
    'lang'               : r'en-GB-oxendict',
    'name'               : r'\w+',
    'namespace'          : r'grammar-notation|asi-rules|annexB',
    'oldids'             : f"{id_pattern}(,{id_pattern})*",
    'rel'                : r'icon',
    'replaces-step'      : id_pattern,
    'rowspan'            : r'\d',
    'src'                : r'img/[-\w.]+',
    'suppress-effects'   : r'user-code',
    'variants'           : r'(\w+([ -]\w+)*)(,\w+([ -]\w+)*)*',
    'width'              : r'\d+',

    'example'            : None,
    'informative'        : None,
    'legacy'             : None,
    'normative'          : None,
    'normative-optional' : None,
    'title'              : None,
}

kind_ = {}
required_attrs_ = {}
optional_attrs_ = {}
content_model_ = {}
for (element_name, (kind, required_attrs, optional_attrs, content_model)) in element_info.items():
    kind_[element_name] = kind
    required_attrs_[element_name] = set(required_attrs.split())
    optional_attrs_[element_name] = set(optional_attrs.split())
    anchored_re = '^(' + content_model + ')$'
    content_model_[element_name] = anchored_re

if __name__ == '__main__':
    text = '<tr><td>foo<emu-xhref="#sec-matchall">`String.prototype.matchAll`</emu-xref> method.</td></tr>'
    shared.install_spec_text(text)
    x = _parse()

# vim: sw=4 ts=4 expandtab
