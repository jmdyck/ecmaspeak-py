
# ecmaspeak-py/HTML.py:
# Parse and validate ecmarkup's flavor of HTML.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re
from html.parser import HTMLParser
from collections import OrderedDict

import shared
from shared import stderr, header, msg_at_posn

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
    header("parsing markup...")
    parser = MyHTMLParser()
    parser.feed(shared.spec_text)
    parser.close()
    return parser.finish()

class MyHTMLParser(HTMLParser):
    def __init__(self):
        # self.k = 0
        HTMLParser.__init__(self)
        # self.curr_node is the deepest node that is currently under construction.
        # That is, of the unfinished/unclosed nodes, it's the most recently started/opened.
        self.curr_node = None
        self.curr_node = self._add_node('#DOC', [])
        # self.reo_only_whitespace = re.compile(r'^\s+$')
        self.START_IS_ALSO_END =  ['meta', 'link', 'br', 'img']

    def finish(self):
        self._end_previous()
        if self.curr_node.element_name == '#DOC':
            self.curr_node.set_end_pos(self._getposn())
        else:
            self._report("at end of file, element still open: " + self.curr_node.element_name)
        return self.curr_node

    # ---------------------------

    def handle_starttag(self, element_name, attrs):
        # print('  '*self.k + "<" + element_name); self.k += 1
        new_node = self._add_node( element_name, attrs)
        if element_name in self.START_IS_ALSO_END:
            # self.curr_node doesn't change
            pass
        else:
            self.curr_node = new_node
            # print('self.curr_node is now', self.curr_node.element_name)

    def handle_startendtag(self, element_name, attrs):
        # print('  '*self.k + "=" + element_name)
        self._report("Self-closing tag")
        new_node = self._add_node( element_name, attrs)
        assert element_name in self.START_IS_ALSO_END
        # self.curr_node doesn't change

    def handle_endtag(self, element_name):
        # (Note that HTMLParser has converted element_name to lower case,
        # so it's not possible to detect case anomalies.)
        # self.k -= 1; print('  '*self.k + "</" + element_name)
        self._end_previous()
        self.curr_node.set_inner_end_pos(self._getposn())
        if element_name != self.curr_node.element_name:
            self._report( "Well-formedness error: got </%s> when the open element is %s" % (element_name, self.curr_node.element_name))
            if self.curr_node.parent is None:
                self._report("self.curr_node.parent is None")
            elif element_name == self.curr_node.parent.element_name:
                self._report("Assuming that </%s> is missing" % self.curr_node.element_name)
                self.curr_node.set_end_pos(self._getposn())
                self.curr_node = self.curr_node.parent.parent
                self.curr_node.set_inner_end_pos(self._getposn())
        else:
            self.curr_node = self.curr_node.parent
            # print('self.curr_node is now', self.curr_node.element_name)

    def handle_data(self, data):
        self._add_node( '#LITERAL', [])
        #
        # Sometime between python 3.2? and 3.5.3, HTMLParser changed:
        # `data` now has entity-references decoded?
        # So if it says '&lt;' in the source doc, we get '<' here.
        # So there's no point complaining about '<'.
        if False and '<' in data:
            pdb.set_trace()
            self._report("maybe change < to &lt;")

    def handle_entityref(self, name):
        self._add_node( '#ENTITYREF', [])

    def handle_charref(self, name):
        self._add_node( '#CHARREF', [])

    def handle_comment(self, data):
        self._add_node( '#COMMENT', [])

    def handle_decl(self, decl):
        self._add_node( '#DECL', [])

    def handle_pi(self, data):
        assert 0
    def handle_unknown_decl(self, data):
        assert 0

    # ---------------------------

    def _add_node(self, node_name, attrs):
        self._end_previous()
        return HNode(self.curr_node, self._getposn(), node_name, attrs)

    def _end_previous(self):
        if not self.curr_node: return
        if self.curr_node.children:
            self.curr_node.children[-1].set_end_pos(self._getposn())
        else:
            self.curr_node.set_inner_start_pos(self._getposn())

    def _report(self, msg):
        posn = self._getposn()
        msg_at_posn(posn, msg)

    def _getposn(self):
        return shared.convert_HTMLParser_getpos_to_posn(self.getpos())

class HNode:
    def __init__(self, parent, start_posn, element_name, attrs):
        self.parent = parent
        self.start_posn = start_posn
        self.element_name = element_name
        self.attrs =  OrderedDict(attrs)
        self.children = []
        if self.parent:
            self.parent.children.append(self)

    def set_end_pos(self, end_posn):
        self.end_posn = end_posn
        # print(repr(shared.spec_text[self.start_posn:self.end_posn]))
        # input()

    def set_inner_start_pos(self, posn):
        self.inner_start_posn = posn

    def set_inner_end_pos(self, posn):
        self.inner_end_posn = posn

    def source_text(self):
        return shared.spec_text[self.start_posn:self.end_posn]

    def inner_source_text(self):
        return shared.spec_text[self.inner_start_posn:self.inner_end_posn]

    def is_element(self):
        return not self.element_name.startswith('#')

    def is_textual(self):
        return (self.element_name in ['#LITERAL', '#ENTITYREF', '#CHARREF'])

    def is_whitespace(self):
        return self.element_name == '#LITERAL' and string_is_whitespace(self.source_text())

    def is_nonwhite_text(self):
        return (
            self.element_name == '#LITERAL' and not string_is_whitespace(self.source_text())
            or
            self.element_name == '#ENTITYREF'
            or
            self.element_name == '#CHARREF'
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
        header("validating markup...")

    if node.element_name in ['#LITERAL', '#CHARREF', '#ENTITYREF']: return

    # First do a pass to figure whether the content of this node
    # is block items or inline items or (anomalously) both.
    node.block_child_element_names = set()
    node.inline_child_element_names = set()
    for child in node.children:
        if child.element_name == '#COMMENT':
            continue
        elif child.element_name in ['#CHARREF', '#ENTITYREF']:
            node.inline_child_element_names.add(child.element_name)
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
        if child.element_name in ['#CHARREF', '#ENTITYREF']:
            x = '#TEXT;'
        elif child.element_name == '#LITERAL':
            if node.inline_child_element_names:
                x = '#TEXT;'
            else:
                assert child.is_whitespace()
                x = '#WS;'
        else:
            x = child.element_name + ';'
        children_names.append(x)

    children_names = ''.join(children_names)
    children_names = re.sub('(#TEXT;)+', '#TEXT;', children_names)
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
        '#DOC'              : ('B', '#DECL;#WS;meta;#WS;((link;|script;|style;)#WS;)+pre;#WS;p;#WS;div;#WS;emu-intro;#WS;(emu-clause;#WS;)+(emu-annex;#WS;)+'),
        'emu-intro'         : ('B', '#WS;h1;#WS;((p;|emu-integration-plans;)#WS;)+'),
        'emu-clause'        : ('B', '#WS;h1;#WS;((div;|emu-alg;|emu-import;|emu-operation-header;|emu-eqn;|emu-figure;|emu-grammar;|emu-motivation;|emu-note;|emu-see-also-para;|emu-table;|figure;|h2;|ol;|p;|pre;|ul;)#WS;)*((emu-clause;|emu-integration-plans;)#WS;)*'),
        'emu-annex'         : ('B', '#WS;h1;#WS;((emu-alg;|emu-grammar;|emu-note;|emu-operation-header;|emu-prodref;|emu-table;|h2;|ol;|p;|ul;)#WS;)*(emu-annex;#WS;)*'),
        'emu-table'         : ('B', '#WS;(emu-caption;#WS;)?table;#WS;'),
        'emu-figure'        : ('B', '#WS;(object;|img;)#WS;'),
        'figure'            : ('B', '#WS;table;#WS;'),
        'table'             : ('B', '#WS;(thead;#WS;)?tbody;#WS;'),
        'tbody'             : ('B', '#WS;(tr;#WS;)+'),
        'thead'             : ('B', '#WS;(tr;#WS;)+'),
        'tr'                : ('B', '(#WS;)?((th;|td;)(#WS;)?)+'),
        'ul'                : ('B', '#WS;(li;#WS;)+'),
        'ol'                : ('B', '#WS;(li;#WS;)+'),
        'object'            : ('B', '#WS;img;#WS;'),

        # block contains blocks or contains inlines, but not both:
        'emu-integration-plans': ('B', '#WS;(p;#WS;)+|(#TEXT;|a;)+'), # PROPOSALS
        'emu-note'             : ('B', '#WS;p;#WS;((div;|emu-alg;|emu-grammar;|emu-table;|figure;|p;|pre;|ul;)#WS;)*|#TEXT;(emu-xref;#TEXT;)?'),
        'li'                   : ('B', '#WS;p;#WS;((emu-alg;|emu-note;|ol;|p;|ul;)#WS;)?|(#TEXT;|a;|br;|code;|dfn;|em;|emu-eqn;|emu-grammar;|emu-xref;|i;|ins;|sub;|sup;|var;)+'), # num-ref: doesn't have to start with TEXT
        'td'                   : ('B', '#WS;((emu-alg;|p;|emu-note;)#WS;)*|(#TEXT;|b;|br;|code;|dfn;|em;|emu-xref;|i;|ins;|sup;)+'),
        'div'                  : ('B', '#WS;((h1;|p;|ul;)#WS;)+|#TEXT;((br;|i;|sup;)#TEXT;)?'),

        # block contains inlines:
        'emu-motivation'       : ('B', '(#TEXT;|a;)+'), # PROPOSALS
        'emu-todo'             : ('B', '(#TEXT;|a;)+'), # PROPOSALS
        'emu-operation-header' : ('B', '(#TEXT;|code;|dfn;|emu-eqn;|emu-xref;|i;|sup;)+'), # my PR
        'emu-alg'              : ('B', '(#TEXT;|a;|b;|code;|del;|emu-grammar;|emu-xref;|figure;|i;|ins;|pre;|sub;|sup;|table;|var;)+'), # BLOCK INCLUSIONS: figure, pre, table
        'emu-caption'          : ('B', '(#TEXT;|emu-xref;)+'),
        'pre'                  : ('B', '#TEXT;|code;'),
        'style'                : ('B', '#TEXT;'),
        'p'                    : ('B', 'img;|(#TEXT;|a;|b;|br;|code;|dfn;|em;|emu-eqn;|emu-grammar;|emu-prodref;|emu-t;|emu-xref;|i;|ins;|sub;|sup;|var;)+'), # the img; is just for the logo at the start, weird.
        'h1'                   : ('B', '(#TEXT;|del;|i;|ins;)+'),
        'h2'                   : ('B', '#TEXT;'),
        'th'                   : ('B', '#TEXT;(sup;#TEXT;)?'),
        'script'               : ('B', '(#TEXT;)?'),

        # block is empty:
        '#DECL'             : ('B', ''),
        'meta'              : ('B', ''),
        'link'              : ('B', ''),
        'img'               : ('B', ''),
        'emu-see-also-para' : ('B', ''),
        'emu-import'        : ('B', ''),

    # ---------------------------------------------
    # can be block or inline, depending on the context:

        'emu-grammar'       : ('A', '(#TEXT;|ins;|del;)+'),
        'emu-prodref'       : ('A', ''),
        'emu-eqn'           : ('A', '#TEXT;(sub;|sup;|#TEXT;)*'),

        'a'                 : ('A', '(#TEXT;|code;|del;|ins;)*'),
        # was inline-only, but then BTerlson added <a id='table-9'></a>
        # Could change it back if he accepts oldids edit.

    # ---------------------------------------------
    # inlines:

        'b'                 : ('I', '(#TEXT;|sub;|sup;)+'),
        'br'                : ('I', ''),
        'code'              : ('I', '(#TEXT;|i;|var;)+'),
        'del'               : ('I', '(#TEXT;|emu-xref;)+'), # PROPOSALS
        'dfn'               : ('I', '(#TEXT;|emu-eqn;)'),
        'em'                : ('I', '#TEXT;'),
        'emu-t'             : ('I', '#TEXT;'),
        'emu-xref'          : ('I', '(#TEXT;)?'),
        'i'                 : ('I', '#TEXT;(sup;#TEXT;)?'),
        'ins'               : ('I', '#TEXT;((a;|emu-xref;|sub;)#TEXT;)?'), # PROPOSALS?
        'sub'               : ('I', '#TEXT;|dfn;'), # dfn; for num-ref
        'sup'               : ('I', '(#TEXT;|sub;)+'), # sub; for num-ref
        'var'               : ('I', '#TEXT;'),

    # ---------------------------------------------
    # other:

        '#COMMENT'          : (None, ''),

}

kind_ = {}
content_model_ = {}
for (element_name, (kind, content_model)) in element_info.items():
    kind_[element_name] = kind
    anchored_re = '^(' + content_model + ')$'
    content_model_[element_name] = anchored_re

# vim: sw=4 ts=4 expandtab
