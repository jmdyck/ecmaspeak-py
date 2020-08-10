#!/usr/bin/python3

# ecmaspeak-py/render_spec.py:
# Generate an HTML version of the spec that approximates the official one.
# 
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, pdb, time
from collections import defaultdict, OrderedDict

import emu_grammars
import shared
from shared import stderr, spec
import misc

_n_tables = 0
_n_figures = 0

def main():
    shared.register_output_dir(sys.argv[1])
    spec.restore()

    prep_xrefs()
    prep_autolinking()
    prep_grammar()

    stderr("render ...")
    global _f
    _f = shared.open_for_output('index.html')
    render_node(spec.doc_node)
    _f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def prep_xrefs():
    stderr("prep_xrefs ...")
    global _default_xref_text_for_fragid_, _title_xref_text_for_fragid_
    _default_xref_text_for_fragid_ = {}
    _title_xref_text_for_fragid_ = {}

    for section in spec.doc_node.each_descendant_named(re.compile('emu-clause|emu-annex')):
        assert 'id' in section.attrs
        fragid = section.attrs['id']
        _default_xref_text_for_fragid_[fragid] = section.section_num
        _title_xref_text_for_fragid_[fragid] = section.section_title

    table_i = 0
    for element in spec.doc_node.each_descendant_named(re.compile('emu-table|emu-import')):
        table_i += 1
        if element.element_name == 'emu-table':
            if 'id' not in element.attrs:
                # No way to xref the table (but it still gets counted).
                continue
            fragid = element.attrs['id']
        elif element.element_name == 'emu-import':
            # Currently, each emu-import (of file foo.html)
            # defines one emu-table (with id 'foo').
            # XXX Really, we should do something more robust.
            href = element.attrs['href']
            fragid = href.replace('.html', '')
        else:
            assert 0
        _default_xref_text_for_fragid_[fragid] = 'Table %d' % table_i

    figure_i = 0
    for emu_figure in spec.doc_node.each_descendant_named('emu-figure'):
        figure_i += 1
        assert 'id' in emu_figure.attrs
        fragid = emu_figure.attrs['id']
        _default_xref_text_for_fragid_[fragid] = 'Figure %d' % figure_i

    for dfn in spec.doc_node.each_descendant_named('dfn'):
        if 'id' in dfn.attrs:
            fragid = dfn.attrs['id']
            term = dfn.inner_source_text()
            _default_xref_text_for_fragid_[fragid] = term

    for emu_alg in spec.doc_node.each_descendant_named('emu-alg'):
        for mo in re.compile(r'\[id="([^"]+)"\]').finditer(emu_alg.source_text()):
            fragid = mo.group(1)
            _default_xref_text_for_fragid_[fragid] = '{STEP-PATH}' # XXX

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def prep_autolinking():
    stderr("prep_autolinking ...")

    plain_words = []
    percent_words = []
    odd_ones = []

    global _replacement_for_term, _fragid_for_term
    _replacement_for_term = {}
    _fragid_for_term = {}

    def register(kind, term, fragid):
        assert term not in _fragid_for_term or term == 'LocalTZA'
        _fragid_for_term[term] = fragid

        if kind == 'aoid':
            xref_attr = 'aoid="%s"' % term
        else:
            xref_attr = 'href="#%s"' % fragid

        if term == 'thisTimeValue':
            # bug in ecmarkup?
            a_href = 'https://tc39.github.io/ecma262/#sec-properties-of-the-date-prototype-object'
        elif term == 'thisBooleanValue':
            a_href = 'https://tc39.github.io/ecma262/#sec-thisbooleanvalue'
        else:
            a_href = '#' + fragid

        _replacement_for_term[term] = (
            r'<emu-xref %s><a href="%s">%s</a></emu-xref>'
            %
            (xref_attr, a_href, term)
        )

    for dfn in spec.doc_node.each_descendant_named('dfn'):
        cc_section = dfn.closest_containing_section()
        term = dfn.inner_source_text()
        if term == '<emu-eqn>_t_<sub>local</sub> = _t_</emu-eqn>':
            # shouldn't even be a dfn?
            continue
        elif term in ['Set', 'type']:
            # skip it.
            continue
        elif term.startswith('LocalTZA('):
            term = 'LocalTZA'

        # Different kinds of terms will be detected (for auto-linking) in different ways...
        if re.fullmatch(r'\w[-\w ]*\w', term) or term in ['\u211d', '\U0001d53d']:
            if 'id' in dfn.attrs:
                # Occurrences of this term should be linked to the dfn itself.
                fragid = dfn.attrs['id']
            else:
                # Link them to the <dfn>'s containing section
                fragid = cc_section.section_id
            plain_words.append(term)

            if term in [
                'abstract operations',
                'agent',
                'constructor',
                'early error',
                'exotic object',
                'property name',
                'realm',
                'strict mode code',
            ]:
                term2 = term.capitalize()
                register('defterm', term2, fragid)
                plain_words.append(term2)

        elif re.fullmatch(r'%(\w+(\.\w+)*)%', term):
            # Occurrences of this term should be linked to the section
            assert not dfn.attrs
            fragid = cc_section.section_id
            percent_words.append(term[1:-1])
        elif re.fullmatch(r'@@\w+', term):
            assert not dfn.attrs
            fragid = cc_section.section_id
            #XXX something.append(term)
        else:
            assert not dfn.attrs
            assert term in ['[[IsHTMLDDA]] internal slot', '%TypedArray% prototype object']
            fragid = cc_section.section_id
            odd_ones.append(term)

        register(('aoid' if 'aoid' in dfn.attrs else 'defterm'), term, fragid)

    plain_words.sort(key=len, reverse=True)
    plain_words_pattern = (
        r'\b('
        +
        '|'.join(plain_words)
        +
        # r')\b'
        r')\b(?!-|\]\])'
    )

    percent_words.sort(key=len, reverse=True)
    # not necessary, because the percents delimit the match
    percent_words_pattern = (
        '%('
        +
        '|'.join(percent_words)
        +
        ')%'
    )

    odd_ones_pattern = (
        '('
        +
        '|'.join(re.escape(odd_one) for odd_one in odd_ones)
        +
        ')'
    )

    # -----------------

    aoids = []
    for thing in spec.doc_node.each_descendant_named(re.compile('emu-clause|emu-annex|emu-eqn')):
        if 'aoid' not in thing.attrs: continue
        aoid = thing.attrs['aoid']
        assert re.fullmatch(r'\w[-\w /:]*\w', aoid)

        if aoid in ['Set', 'Type', 'UTC', 'Call']:
            aoid_pattern = aoid + r'(?= *\()'
        else:
            aoid_pattern = aoid
        if aoid in aoids: stderr("multiple definitions for", aoid)
        aoids.append(aoid_pattern)

        if 'id' in thing.attrs:
            id = thing.attrs['id']
        else:
            cc_section = thing.closest_containing_section()
            id = cc_section.attrs['id']
        register('aoid', aoid, id)

    aoids.sort(key=len, reverse=True)
    aoids_pattern = (
        r'\b('
        +
        '|'.join(aoids)
        +
        # r')\b'
        # r')(?= *\()'
        r')\b(?!\]\])'
    )

    # -----------------

    global _defined_term_pattern
    _defined_term_pattern = '(%s|%s|%s|%s)' % (
        odd_ones_pattern,
        percent_words_pattern,
        plain_words_pattern,
        aoids_pattern
    )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def render_node(node):
    if node.element_name == '#LITERAL':
        render_literal_node(node)

    elif node.element_name == 'meta':
        assert node.attrs.get('charset','') == 'utf-8'
        put('<meta charset="utf-8">')

    elif node.element_name in ['link', 'script']:
        text = shared.spec_text[node.start_posn:node.end_posn]
        text = re.sub(' (href|src)="(img|ecma)', r' \1="https://tc39.es/ecma262/\2', text)
        put(text)

    elif node.element_name in ['#COMMENT', '#DECL', 'br', 'img']:
        # `node` is either:
        # - a comment,
        # - a doctype decl,
        # - a self-closing tag: <br> <img ...> <link ...> <meta ...>
        put_node(node)

    elif node.element_name in ['style']:
        put_node(node)

    elif node.element_name == 'code':
        render_code(node)

    elif node.element_name == 'emu-alg':
        render_emu_alg(node)

    elif node.element_name == 'emu-grammar':
        render_emu_grammar(node)

    elif node.element_name == 'emu-prodref':
        render_emu_prodref(node)

    elif node.element_name == 'emu-caption':
        assert node.parent.element_name == 'emu-table'
        # Handled under emu-table

    elif node.element_name == 'pre' and node.attrs.get('class', '') == 'metadata':
        pubyear = '2020'
        today = time.strftime("%B %d, %Y")
        put(f'''
<title>ECMAScript® {pubyear} Language&nbsp;Specification</title>
</head>
<body>
<div id="spec-container">
<h1 class="version first">Draft ECMA-262 / {today}</h1>
<h1 class="title">ECMAScript® {pubyear} Language&nbsp;Specification</h1>
        ''')

    elif node.element_name == '#DOC':
        for child in node.children:
            render_node(child)
        put(licence_annex)
        put('</div></body>')

    else:

        if node.element_name in ['emu-clause', 'emu-annex']:
            notes = [
                note
                for x in [node] + node.numless_children
                for block in x.block_children
                for note in block.each_descendant_named('emu-note')
            ]
            if len(notes) == 0:
                pass
            elif len(notes) == 1:
                pass
                # XXX ?
                # [note] = notes
                # note.note_number = None
            else:
                for (i, note) in enumerate(notes):
                    note.note_number = i+1

        elif node.element_name == 'emu-eqn':
            if node.parent.element_name != 'emu-clause':
                node.attrs['class'] = 'inline'

        elif node.element_name in ['dfn', 'em', 'i']:
            # pointless insertion of space
            put(' ')

        elif node.element_name == 'h1':
            p = node.parent
            assert p.element_name in ['emu-clause', 'emu-annex', 'emu-intro', 'div']
            if 'oldids' in p.attrs:
                put('<span id="%s"></span>' % p.attrs['oldids'])

        # ---------------------------------------------------
        # start tag:
        # put_range(node.start_posn, node.inner_start_posn)
        put_start_tag_for_node(node)

        # ---------------------------------------------------
        # stuff after start tag:
        if node.element_name == 'h1':
            section = node.parent
            if section.element_name != 'div':
                put('<span class="secnum">%s</span>' % section.section_num)

        elif node.element_name == 'emu-note':
            label = ('Note %d' % node.note_number) if hasattr(node, 'note_number') else 'Note'
            put('<span class="note">%s</span><div class="note-contents">' % label)

        elif node.element_name == 'emu-table':
            c = node.children[1]
            if c.element_name == 'emu-caption':
                assert 'caption' not in node.attrs
                caption_text = c.inner_source_text()
            else:
                caption_text = enhance_text(node.attrs['caption'], node)
            informative = 'informative' in node.attrs
            global _n_tables
            _n_tables += 1
            inf = ' (Informative)' if informative else ''
            put(r'<figure><figcaption>Table %d%s: %s</figcaption>' % (
                _n_tables, inf, caption_text))

        elif node.element_name == 'emu-figure':
            global _n_figures
            _n_figures += 1
            inf = ' (Informative)' if 'informative' in node.attrs else ''
            put('<figure><figcaption>Figure %d%s: %s</figcaption>' % (
                _n_figures, inf, node.attrs['caption']))

        elif node.element_name == 'emu-eqn':
            if node.parent.element_name == 'emu-clause':
                put('<div>')
            elif node.parent.element_name in ['p', 'li', 'dfn', 'dd']:
                # (r'<emu-eqn>',    r' <emu-eqn class="inline">'),
                pass
            else:
                assert 0
            

        elif node.element_name == 'emu-xref':
            href = node.attrs['href']
            assert href.startswith('#')
            fragid = href[1:]
            put('<a href="%s">' % href)
            if not node.children:
                if 'title' in node.attrs:
                    xref_text = enhance_text(_title_xref_text_for_fragid_[fragid], node)
                else:
                    xref_text = _default_xref_text_for_fragid_[fragid]
                put(xref_text)

        # ---------------------------------------------------
        # content:
        for child in node.children:
            render_node(child)

        # ---------------------------------------------------
        # stuff before end tag:

        if node.element_name == 'emu-table':
            put('</figure>')
        elif node.element_name == 'emu-figure':
            put('</figure>')
        elif node.element_name == 'emu-note':
            put('</div>')
        elif node.element_name == 'emu-eqn' and node.parent.element_name == 'emu-clause':
            put('</div>')
        elif node.element_name in ['td', 'th', 'li']:
            # pointless insertion of whitespace
            x = node.children[-1]
            mo = re.search(r'\n *$', x.source_text())
            if mo:
                put(mo.group(0))
        elif node.element_name == 'emu-xref':
            put('</a>')

        # ---------------------------------------------------
        # end tag:
        put_range(node.inner_end_posn, node.end_posn)

licence_annex = '''\
<emu-annex id="sec-copyright-and-software-license">
      <h1><span class="secnum">H</span>Copyright &amp; Software License</h1>
      <p class="ECMAaddress">Ecma International</p>
<p class="ECMAaddress">Rue du Rhone 114</p>
<p class="ECMAaddress">CH-1204 Geneva</p>
<p class="ECMAaddress">Tel: +41 22 849 6000</p>
<p class="ECMAaddress">Fax: +41 22 849 6001</p>
<p class="ECMAaddress">Web:  <a href="https://ecma-international.org/">https://ecma-international.org/</a></p>

      <h2>Copyright Notice</h2>
      <p>© 2018 Ecma International</p>

<p>This draft document may be copied and furnished to others, and derivative works that comment on or otherwise explain it or assist in its implementation may be prepared, copied, published, and distributed, in whole or in part, without restriction of any kind, provided that the above copyright notice and this section are included on all such copies and derivative works. However, this document itself may not be modified in any way, including by removing the copyright notice or references to Ecma International, except as needed for the purpose of developing any document or deliverable produced by Ecma International.</p>

<p>This disclaimer is valid only prior to final version of this document. After approval all rights on the standard are reserved by Ecma International.</p>

<p>The limited permissions are granted through the standardization phase and will not be revoked by Ecma International or its successors or assigns during this time.</p>

<p>This document and the information contained herein is provided on an "AS IS" basis and ECMA INTERNATIONAL DISCLAIMS ALL WARRANTIES, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO ANY WARRANTY THAT THE USE OF THE INFORMATION HEREIN WILL NOT INFRINGE ANY OWNERSHIP RIGHTS OR ANY IMPLIED WARRANTIES OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE.</p>

      <h2>Software License</h2>
      <p>All Software contained in this document ("Software") is protected by copyright and is being made available under the "BSD License", included below. This Software may be subject to third party rights (rights from parties other than Ecma International), including patent rights, and no licenses under such third party rights are granted under this license even if the third party concerned is a member of Ecma International. SEE THE ECMA CODE OF CONDUCT IN PATENT MATTERS AVAILABLE AT https://ecma-international.org/memento/codeofconduct.htm FOR INFORMATION REGARDING THE LICENSING OF PATENT CLAIMS THAT ARE REQUIRED TO IMPLEMENT ECMA INTERNATIONAL STANDARDS.</p>

<p>Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:</p>

<ol>
  <li>Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.</li>
  <li>Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.</li>
  <li>Neither the name of the authors nor Ecma International may be used to endorse or promote products derived from this software without specific prior written permission.</li>
</ol>

<p>THIS SOFTWARE IS PROVIDED BY THE ECMA INTERNATIONAL "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL ECMA INTERNATIONAL BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.</p>

    </emu-annex>
'''

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def put_start_tag_for_node(node):
    put(
        '<'
        +
        node.element_name
        +
        ''.join(
            (' ' + a_name) if a_val is None else (' %s="%s"' % (a_name, a_val))
            for (a_name, a_val) in node.attrs.items()
        )
        +
        '>'
    )

def render_code(code):
    is_javascript = (code.attrs.get('class', '') == 'javascript')
    if is_javascript:
        code.attrs['class'] += ' hljs'
    put_start_tag_for_node(code)
    indent = None
    for (i, child) in enumerate(code.children):
        if child.element_name == '#LITERAL':
            t = child.source_text()
            if i == 0:
                mo = re.match(r'(?s)(\n +)(.+)', t)
                if mo:
                    (indent, rest) = mo.groups()
                    t = rest
            if i == len(code.children)-1:
                t = t.rstrip()
            if indent is not None:
                t = t.replace(indent, '\n')
            if is_javascript:
                # t = re.sub(r'\b(function\*) (\w+)\(([^()]+)\) ',
                #     r'<span class="hljs-function">\1 <span class="hljs-title>\2</span>(<span class="hljs-params">\3</span>) </span>',
                #     t
                # )
                t = re.sub(r'''(?x)
                    (?P<string>"[^"]*")
                    |
                    \b(?P<number>\d+)\b
                    |
                    \b(?P<keyword>await|const|constructor|continue|else|for|function|if|instanceof|let|new|of|return|super|typeof|yield)\b
                    |
                    \b(?P<built_in>Date|Function|JSON|Object|Reflect|Set|Symbol|eval)
                    |
                    \b(?P<literal>null|undefined)
                    |
                    (?P<comment>// .+)
                ''', hljs_repl, t)
            put(t)
        else:
            put_node(child)
    put('</code>')

def hljs_repl(mo):
    key = mo.lastgroup
    content = mo.group(key)
    return '<span class="hljs-%s">%s</span>' % (key, content)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def render_emu_alg(emu_alg):
    emu_grammars_in_this_emu_alg = [
        child
        for child in emu_alg.children
        if child.element_name == 'emu-grammar'
    ]
    assert 0 <= len(emu_grammars_in_this_emu_alg) <= 2
    emu_grammar_i = 0

    body = emu_alg.inner_source_text()

    body = body.rstrip()

    lines = [
        (len(moo.group(1)), moo.group(2), moo.group(3))
        for moo in re.compile('\n( *)(?:(\d+\.|\*) )?(.*)').finditer(body)
    ]

    def handle_level(start_i, end_i):
        nonlocal lines

        assert start_i <= end_i

        if start_i == end_i: return ''

        is_at_this_level = [
            i
            for i in range(start_i, end_i)
            if lines[i][0] == lines[start_i][0]
        ]

        if lines[start_i][1] is None:
            myresult = ''
            for i in range(start_i, end_i):
                myresult += '\n' + (' '*lines[i][0]) + expand_step_body(lines[i][2])

        else:
            list_type = 'ul' if lines[start_i][1] == '*' else 'ol'
            myresult = '\n<%s>' % list_type
            for (i1, i2) in misc.each_adjacent_pair_from(is_at_this_level + [end_i]):
                # item runs from i1 up to but not incl i2
                myresult += (
                    '\n<li>'
                    + expand_step_body(lines[i1][2])
                    + handle_level(i1+1, i2)
                    + '</li>'
                )
            myresult += '\n</%s>' % list_type

        return myresult

    def expand_step_body(step_body):

        # emu-grammar can occur in emu-alg.
        # Handle this first (before enhance_text) so that emu-grammar notation
        # doesn't get mishandled as emu-alg notation.
        # E.g. within emu-grammar,
        # `foo` should become <emu-t>foo</emu-t>, not <code>foo</code>.
        #
        def replfunc(mo):
            nonlocal emu_grammar_i
            emu_grammar = emu_grammars_in_this_emu_alg[emu_grammar_i]
            emu_grammar_i += 1
            return expand_emu_grammar(emu_grammar)

        step_body = re.sub(r'<emu-grammar>(.+?)</emu-grammar>', replfunc, step_body)

        step_body = enhance_text(step_body, emu_alg)

        step_body = re.sub(
            r'(<emu-xref href="#([^<>]+)"( title)?>)(</emu-xref>)',
            lambda mo: (
                mo.group(1)
                +
                ('<a href="#%s">' % mo.group(2))
                +
                (
                    _title_xref_text_for_fragid_[mo.group(2)]
                    if
                    mo.group(3)
                    else
                    _default_xref_text_for_fragid_[mo.group(2)]
                )
                +
                '</a>'
                +
                mo.group(4)
            ),
            step_body
        )

        return step_body

    listified_text = handle_level(0, len(lines))
    result = '<emu-alg>' + listified_text + '</emu-alg>'
    put(result)
    assert emu_grammar_i == len(emu_grammars_in_this_emu_alg)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def render_literal_node(node):
    assert node.element_name == '#LITERAL'
    text = shared.spec_text[node.start_posn: node.end_posn]
    assert not text.startswith('<')

    if node.parent.element_name == 'emu-eqn':
        text = text.rstrip().replace('\n', '</div>\n<div>')

    text = enhance_text(text, node.parent)

    put(text)

# ------------------------------------------------------------------------------

def enhance_text(text, node):

    cc_section = node.closest_containing_section()

    namespace = get_grammar_namespace(cc_section) if cc_section else ''
    id_insert = '' if namespace == '' else (namespace + '-')

    def replace_defined_term(mo):
        whole_match = mo.group(0)
        term = mo.group(1)
        # if node.element_name == 'emu-table' and whole_match == 'ToBoolean': pdb.set_trace()
        # if whole_match == 'HourFromTime': pdb.set_trace()
        # if '[' in term: pdb.set_trace()
        if term not in _fragid_for_term:
            stderr(f"no fragid for term {term!r} ")
            return whole_match

        term_fragid = _fragid_for_term[term]
        if node.element_name == 'p' and cc_section and term_fragid == cc_section.section_id:
            # This a reference to the term from within
            # the 'top' of the section in which it's defined.
            # In this case, we don't make the reference a link,
            # because the definition is presumably nearby.
            # (It's unclear what the actual rule is.)
            return whole_match
        elif 'id' in node.attrs and node.attrs['id'] == term_fragid:
            return whole_match
        elif node.element_name in [
            'dfn',      # Don't linkify the definition itself.
            'h1',       # Don't put links in clause-titles.
            'emu-xref', # Don't linkify something that's already linked.
        ]:
            return whole_match
        else:
            return _replacement_for_term[term]

    def handle_non_emd_text(text):
        text = misc.re_sub_many(
            [
                (_defined_term_pattern, replace_defined_term),

                (r' \? ', r' ?&nbsp;'),
                (r' ! ', r' !&nbsp;'),
            ],
            text
        )
        return text

    def expand_emd_span(t):
        delimiter = t[0]
        content = t[1:-1].replace('>', '&gt;')

        opt_attrs = ''

        if delimiter == '|':
            mo = re.fullmatch(r'(\w+?)(_opt)?(?:\[([^][]+)\])?', content)
            (nt_name, optopt, params) = mo.groups()
            content = maybe_link_to_nt(nt_name, namespace)
            mods_content = ''
            if optopt:
                opt_attrs += ' optional=""'
                mods_content += '<emu-opt>opt</emu-opt>'
            if params:
                opt_attrs += ' params="%s"' % params
                mods_content += '<emu-params>[%s]</emu-params>' % params
            if mods_content:
                content += '<emu-mods>%s</emu-mods>' % mods_content

        element_name = {
            '*': 'emu-val',
            '~': 'emu-const',
            '|': 'emu-nt',
            '_': 'var',
            '`': 'code',
        }[delimiter]

        return '<%s%s>%s</%s>' % (element_name, opt_attrs, content, element_name)

    result = ''
    posn = 0
    for mo in re.compile(r'''(?x)
        ~[][\w-]+~
        | `[^`]+`
        | \*[-\w\x20+&;"]+\*
        | \|\w+(\[[^][]+\])?\|
        | \b_[A-Za-z]\w*_(\b|(?=th\b))
    ''').finditer(text):
        (emd_start, emd_end) = mo.span()
        result += handle_non_emd_text(text[posn:emd_start])
        result += expand_emd_span(text[emd_start:emd_end])
        posn = emd_end
    result += handle_non_emd_text(text[posn:len(text)])

    result = expand_char_refs(result)

    result = re.sub(r'\\([~\\])', r'\1', result)
    # result = result.replace('\u005c\u005c', '\u005c') # backslashes

    return result

def expand_char_refs(text):
    return misc.re_sub_many(
        [
            (r'&#x17f;',      r'ſ'),
            (r'&divide;',     r'÷'),
            (r'&frac12;',     r'½'),
            (r'&ge;',         r'≥'),
            (r'&hellip;',     r'…'),
            (r'&infin;',      r'∞'),
            (r'&isin;',       r'∈'),
            (r'&laquo;',      r'«'),
            (r'&raquo;',      r'»'),
            (r'&ldquo;',      r'“'),
            (r'&le;',         r'≤'),
            (r'&mdash;',      r'—'),
            (r'&ndash;',      r'–'),
            (r'&ne;',         r'≠'),
            (r'&notin;',      r'∉'),
            (r'&pi;',         r'π'),
            (r'&rarr;',       r'→'),
            (r'&rdquo;',      r'”'),
            (r'&szlig;',      r'ß'),
            (r'&times;',      r'×'),
            (r'&trade;',      r'™'),
        ],
        text
    )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

_annexA_production_for_ = {}
_something = defaultdict(set)
_lhs_nts_in_namespace_ = defaultdict(set)

def prep_grammar():
    stderr("prep_grammar ...")
    for emu_grammar in spec.doc_node.each_descendant_named('emu-grammar'):
        ns = get_grammar_namespace(emu_grammar)
        trimmed_body = emu_grammars.trim_newlines(emu_grammar.inner_source_text())
        for production in re.split(r'\n{2,}', trimmed_body):
            mo = re.match(r'^ *(\w+)', production)
            assert mo
            lhs_nt = mo.group(1)
            _lhs_nts_in_namespace_[ns].add(lhs_nt)
            fragid = fragid_for_nt_def(lhs_nt, ns)
            _default_xref_text_for_fragid_[fragid] = '<emu-nt>' + lhs_nt + '</emu-nt>'

def maybe_link_to_nt(nt, curr_namespace):
    fragid = fragid_for_nt_ref(nt, curr_namespace)
    if fragid is None:
        return nt
    else:
        return '<a href="#%s">%s</a>' % (fragid, nt)

def fragid_for_nt_ref(nt, curr_namespace):
    # Return a fragment identifier that will resolve to
    # the appropriate defining occurrence of `nt`,
    # when referenced from within `curr_namespace`.
    # Or None if no such defining occurrence exists.

    if nt in _lhs_nts_in_namespace_[curr_namespace]:
        # `nt` is defined in the current namespace.
        def_namespace = curr_namespace

    elif nt in _lhs_nts_in_namespace_['']:
        # `nt` is not defined in the current namespace,
        # but it is defined in the main namespace.
        def_namespace = ''

    else:
        # `nt` isn't defined anywhere?
        return None

    return fragid_for_nt_def(nt, def_namespace)

def fragid_for_nt_def(nt, def_namespace):
    if def_namespace == '':
        return 'prod-%s' % nt
    else:
        return 'prod-%s-%s' % (def_namespace, nt)

# --------------------------------------------------------------------------

def render_emu_grammar(emu_grammar):
    # pointless insertion of whitespace
    # if emu_grammar.parent.element_name == 'p': put(' ')
    # Sometimes inserted, sometimes not -- not sure what the 'rule' is.

    put(expand_emu_grammar(emu_grammar))

# --------------------------------------------------------------------------

_prod1_for_rhs_id_ = {}

def expand_emu_grammar(emu_grammar):
    emu_grammar_type = emu_grammar.attrs.get('type', 'use')

    namespace = get_grammar_namespace(emu_grammar.parent)
    id_insert = '' if namespace == '' else (namespace + '-')

    ex_start_tag = shared.spec_text[emu_grammar.start_posn:emu_grammar.inner_start_posn]
    ex_end_tag = '</emu-grammar>'

    _emu_rhs_for_label = {} # see under RHS_LINE

    def expand_gnode(gnode):
        st = gnode.source_text()
        expanded_children = [expand_gnode(c) for c in gnode.children]

        if gnode.kind == 'BLOCK_PRODUCTIONS':
            return '\n'.join(expanded_children)

        elif gnode.kind in ['MULTILINE_PRODUCTION', 'ONELINE_PRODUCTION']:
            (gnt, colons, rest) = gnode.children
            (nt, optional_params, _) = gnt.children
            lhs_nt_name = nt.source_text()

            prodn_attrs = OrderedDict()

            # name
            prodn_attrs['name'] = lhs_nt_name

            # params
            # production params appear in 3 places:
            #   attr of the <emu-production>,
            #   attr of the <emu-nt>,
            #   <emu-params> in <emu-mods> in <emu-nt>
            if optional_params.kind == 'OMITTED_OPTIONAL':
                pass
            else:
                prodn_attrs['params'] = ', '.join(param.source_text() for param in optional_params.children)

            # type
            n_colons = len(colons.source_text())
            if n_colons == 2:
                prodn_attrs['type'] = 'lexical'
            elif n_colons == 3:
                prodn_attrs['type'] = 'regexp'

            # oneof
            if rest.kind in ['MULTILINE_ONE_OF', 'ONELINE_ONE_OF']:
                prodn_attrs['oneof'] = ''

            # collapsed
            elif gnode.kind == 'ONELINE_PRODUCTION':
                prodn_attrs['collapsed'] = ''

            # id
            if (
                emu_grammar_type
                and
                lhs_nt_name not in _something[namespace]
            ):
                # This is the first production for `lhs_nt_name` in `namespace`.
                # So it's the one that links should point to.
                prodn_attrs['id'] = 'prod-%s%s' % (id_insert, lhs_nt_name)
                _something[namespace].add(lhs_nt_name)

            # class
            if emu_grammar.parent.element_name in ['p', 'li', 'emu-alg']:
                prodn_attrs['class'] = ' inline'

            if gnode.kind == 'ONELINE_PRODUCTION' and rest.kind != 'ONELINE_ONE_OF':
                # sigh
                [a,b,c] = expanded_children
                expanded_children = [a, b, f'<emu-rhs>{c}</emu-rhs>']

            emu_prodn_start_tag = (''
                + '<emu-production'
                + ''.join(
                    ' %s="%s"' % (attr_name, attr_val)
                    for (attr_name, attr_val) in prodn_attrs.items()
                )
                + '>'
            )
            emu_prodn_end_tag = '</emu-production>'

            emu_production = (''
                + emu_prodn_start_tag
                + '\n    '
                + ''.join(expanded_children)
                + '\n'
                + emu_prodn_end_tag
            )

            nonlocal _emu_rhs_for_label
            for (label, emu_rhs) in _emu_rhs_for_label.items():
                _prod1_for_rhs_id_[(lhs_nt_name, label)] = (''
                    + emu_prodn_start_tag
                    + '\n    '
                    + ''.join(expanded_children[:-1])
                    + emu_rhs
                    + emu_prodn_end_tag
                )
            _emu_rhs_for_label = {}

            if namespace == '' and emu_grammar_type == 'definition':
                if lhs_nt_name in _annexA_production_for_:
                    assert lhs_nt_name == 'DoubleStringCharacter' # in JSON.parse
                    stderr('multiple def prodns:', lhs_nt_name)
                else:
                    _annexA_production_for_[lhs_nt_name] = emu_production

                    # ex_body += (
                    #     ('\n' if pi > 0 else '')
                    #     +
                    #     production_element
                   #  )

            return emu_production

        elif gnode.kind == 'MULTILINE_RHSS':
            return '\n    '.join(expanded_children)

        elif gnode.kind == 'RHS_ITEMS':
            if hasattr(gnode, 'parent'): stderr(gnode.parent.kind)
            return ''.join(expanded_children)

        elif gnode.kind == 'RHS_LINE':
            (optional_guard, _, optional_label) = gnode.children
            if optional_guard.kind == 'OMITTED_OPTIONAL':
                maybe_constraints_attr = ''
            else:
                constraints = ', '.join(param.source_text() for param in optional_guard.children)
                maybe_constraints_attr = f' constraints="{constraints}"'

            emu_rhs = (''
                + f'<emu-rhs{maybe_constraints_attr}>'
                + ''.join(expanded_children)
                + '</emu-rhs>'
            )

            if optional_label.kind != 'OMITTED_OPTIONAL':
                label = optional_label.source_text()[1:]
                assert label not in _emu_rhs_for_label
                _emu_rhs_for_label[label] = emu_rhs

            return emu_rhs


        elif gnode.kind == 'PARAMS':
            return f'<emu-constraints>{st}</emu-constraints>'

        elif gnode.kind in ['MULTILINE_ONE_OF', 'ONELINE_ONE_OF']:
            return '<emu-oneof>one of</emu-oneof><emu-rhs>' + ''.join(expanded_children) + '</emu-rhs>'

        elif gnode.kind in ['LINES_OF_BACKTICKED_THINGS', 'BACKTICKED_THINGS']:
            return ''.join(expanded_children)


        # -----------------------------------------------------------

        elif gnode.kind == 'GNT':
            (nt, optional_params, optional_opt) = gnode.children

            nt_name = nt.source_text()
            maybe_link = maybe_link_to_nt(nt_name, namespace)

            emu_mods_content = ''

            if optional_params.kind == 'OMITTED_OPTIONAL':
                maybe_params_attr = ''
            else:
                params = ', '.join(param.source_text() for param in optional_params.children)
                maybe_params_attr = ' params="%s"' % params
                emu_mods_content += '<emu-params>[%s]</emu-params>' % params

            if optional_opt.source_text() == '':
                maybe_optional_attr = ''
            else:
                maybe_optional_attr = ' optional=""'
                emu_mods_content += '<emu-opt>opt</emu-opt>'

            if emu_mods_content:
                maybe_emu_mods_child = '<emu-mods>' + emu_mods_content + '</emu-mods>'
            else:
                maybe_emu_mods_child = ''

            return '<emu-nt%s%s>%s%s</emu-nt>' % (maybe_params_attr, maybe_optional_attr, maybe_link, maybe_emu_mods_child)

        elif gnode.kind == 'NT_BUT_NOT':
            [ex_base, ex_exclusion] = expanded_children

            if ' or ' in ex_exclusion:
                return f'{ex_base}<emu-gmod>but not one of {ex_exclusion}</emu-gmod>'
            else:
                return f'{ex_base}<emu-gmod>but not {ex_exclusion}</emu-gmod>'

        elif gnode.kind == 'NT':
            nt_name = st
            maybe_link = maybe_link_to_nt(nt_name, namespace)
            return f'<emu-nt>{maybe_link}</emu-nt>'

        elif gnode.kind == 'COLONS':
            return f"<emu-geq>{st}</emu-geq>"

        elif gnode.kind == 'BACKTICKED_THING':
            return f"<emu-t>{st[1:-1].replace('>','&gt;')}</emu-t>"

        # emu-gann:

        elif gnode.kind == 'EMPTY':
            return '<emu-gann>[empty]</emu-gann>'

        elif gnode.kind in ['NLTH', 'NLTH_BAR']:
            return '<emu-gann>[no <emu-nt><a href="#prod-LineTerminator">LineTerminator</a></emu-nt> here]</emu-gann>'

        elif gnode.kind == 'LAC_SET':
            [exp_operand] = expanded_children
            return f'<emu-gann>[lookahead ∉ {exp_operand}]</emu-gann>'

        elif gnode.kind == 'LAC_SINGLE':
            (exp_operator, exp_operand) = expanded_children
            return f'<emu-gann>[lookahead {exp_operator} {exp_operand}]</emu-gann>'

        elif gnode.kind == 'LAC_SINGLE_OP':
            return {
                '==': '=',
                '!=': '≠',
            }[st]

        elif gnode.kind == 'SET_OF_TERMINAL_SEQ':
            return '{ ' + ', '.join(expanded_children) + ' }'

        elif gnode.kind == 'TERMINAL_SEQ':
            return ''.join(expanded_children)

        # emu-gprose:

        elif gnode.kind == 'U_ANY':
            return '<emu-gprose>any Unicode code point</emu-gprose>'

        elif gnode.kind == 'U_PROP':
            return f'<emu-gprose>any Unicode code point with the Unicode property “{gnode.groups[0]}”</emu-gprose>'

        elif gnode.kind == 'U_RANGE':
            return f'<emu-gprose>any Unicode code point in the inclusive range {gnode.groups[0]} to {gnode.groups[1]}</emu-gprose>'

        elif gnode.kind == 'NAMED_CHAR':
            return f'<emu-gprose>{st}</emu-gprose>'

        # emu-gmod:

        elif gnode.kind == 'BUT_ONLY':
            return f'<emu-gmod>but only if {gnode.groups[0]}</emu-gmod>'

        # --------

        elif gnode.kind == 'EXCLUDABLES':
            return ' or '.join(expanded_children)

        elif gnode.kind == 'OMITTED_OPTIONAL':
            return ''

        elif gnode.kind == 'LABEL':
            return ''

        elif gnode.kind in ['OPTIONAL_OPT', 'PARAM', 'OPTIONAL_PREFIX', 'PARAM_NAME']:
            return "[DOESN'T MATTER, ISN'T USED]"

        else:
            assert 0

    ex_body = expand_gnode(emu_grammar._gnode)

    return ex_start_tag + ex_body + ex_end_tag

# --------------------------------------------------------------------------

def get_grammar_namespace(node):
    namespace_root = node.nearest_ancestor_satisfying(
        lambda node: 'namespace' in node.attrs
    )
    if namespace_root is None:
        return ''
    else:
        return namespace_root.attrs['namespace']

# ------------------------------------------------------------------------------

def render_emu_prodref(emu_prodref):
    nt_name = emu_prodref.attrs['name']
    if 'a' in emu_prodref.attrs:
        rhs_id = emu_prodref.attrs['a']
        prod_text = _prod1_for_rhs_id_[(nt_name, rhs_id)]
        put(prod_text)
    else:
        prod_text = _annexA_production_for_[nt_name]
        prod_text = re.sub(' id="[^<>]*"', '', prod_text)
        if emu_prodref.parent.element_name == 'p':
            a = emu_prodref.attrs.get('a', None)
            if a: prod_text = re.sub('>', ' a="%s">' % a, prod_text, count=1)
            prod_text = re.sub('>', ' class=" inline" collapsed="">', prod_text)
        put(prod_text)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def put_node(node):
    put_range(node.start_posn, node.end_posn)

def put_range(start, end):
    text = shared.spec_text[start:end]
    put(text)

def put(text):
    _f.write(text)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

main()

# vim: sw=4 ts=4 expandtab
