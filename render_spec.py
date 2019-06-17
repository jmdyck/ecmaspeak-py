#!/usr/bin/python3

# ecmaspeak-py/render_spec.py:
# Generate an HTML version of the spec that approximates the official one.
# 
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, pdb
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

    for dfn in spec.doc_node.each_descendant_named('dfn'):
        if 'id' in dfn.attrs:
            fragid = dfn.attrs['id']
            term = dfn.inner_source_text()
            _default_xref_text_for_fragid_[fragid] = term

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

        if re.fullmatch(r'\w[-\w ]*\w', term):
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

        elif re.fullmatch(r'%(\w+)%', term):
            # link references to the section
            fragid = cc_section.section_id
            percent_words.append(term[1:-1])
        else:
            assert term == '[[IsHTMLDDA]] internal slot'
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
        assert node.attrs.get('charset','') == 'ascii'
        put('<meta charset="utf-8">')

    elif node.element_name in ['#COMMENT', '#DECL', 'br', 'img', 'link']:
        # `node` is either:
        # - a comment,
        # - a doctype decl,
        # - a self-closing tag: <br> <img ...> <link ...> <meta ...>
        put_node(node)

    elif node.element_name in ['style', 'script']:
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
        put('''
<title>ECMAScript® 2019 Language&nbsp;Specification</title>
</head>
<body>
<div id="spec-container">
<h1 class="version first">Draft ECMA-262 / March 21, 2018</h1>
<h1 class="title">ECMAScript® 2019 Language&nbsp;Specification</h1>
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
            elif node.parent.element_name in ['p', 'li', 'dfn']:
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
        step_body = re.sub(
            r'<emu-grammar>(.+?)</emu-grammar>',
            lambda mo: (
                '<emu-grammar>%s</emu-grammar>' %
                expand_emu_grammar_body(mo.group(1), None, emu_alg)
            ),
            step_body
        )

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

    put_range(emu_grammar.start_posn, emu_grammar.inner_start_posn)
    put(
        expand_emu_grammar_body(
            emu_grammar.inner_source_text(),
            emu_grammar.attrs.get('type', 'use'),
            emu_grammar.parent
        )
    )
    put('</emu-grammar>')

# --------------------------------------------------------------------------

_prod1_for_rhs_id_ = {}

def expand_emu_grammar_body(emu_grammar_body, emu_grammar_type, emu_grammar_parent):

    result = ''

    trimmed_body = emu_grammars.trim_newlines(emu_grammar_body)

    namespace = get_grammar_namespace(emu_grammar_parent)
    id_insert = '' if namespace == '' else (namespace + '-')

    for (pi, production) in enumerate(re.split(r'\n{2,}', trimmed_body)):
        mo = re.fullmatch(r'(?s) *([^:]+?) +(:+) *(.+)', production)
        (pre, colons, post) = mo.groups()

        mo = re.fullmatch('(\w+)(?:\[([\w, ]+)\])?', pre)
        (lhs_nt, params) = mo.groups()

        prodn_attrs = OrderedDict()
        prodn_attrs['name'] = lhs_nt
        if params:
            # prodn params appear in 3 places:
            # attr of the <emu-production>,
            # attr of the <emu-nt>,
            # <emu-params> in <emu-mods> in <emu-nt>
            prodn_attrs['params'] = params
            opt_lhs_nt_attrs = ' params="%s"' % params
            opt_mods = '<emu-mods><emu-params>[%s]</emu-params></emu-mods>' % params
        else:
            opt_lhs_nt_attrs = ''
            opt_mods = ''

        if len(colons) == 2:
            prodn_attrs['type'] = 'lexical'
        elif len(colons) == 3:
            prodn_attrs['type'] = 'regexp'

        if post.startswith('one of'):
            prodn_attrs['oneof'] = ''
            post = post[6:]
        elif '\n' not in production:
            prodn_attrs['collapsed'] = ''

        if (
            emu_grammar_type
            and
            lhs_nt not in _something[namespace]
        ):
            # This is the first production for `lhs_nt` in `namespace`.
            # So it's the one that links should point to.
            prodn_attrs['id'] = 'prod-%s%s' % (id_insert, lhs_nt)
            _something[namespace].add(lhs_nt)

        if emu_grammar_parent.element_name in ['p', 'li', 'emu-alg']:
            prodn_attrs['class'] = ' inline'


        production_template = (
            '<emu-production'
            +
            ''.join(
                ' %s="%s"' % (attr_name, attr_val)
                for (attr_name, attr_val) in prodn_attrs.items()
            )
            +
            '>\n'
            +
            '    '
            +
            '<emu-nt%s>%s%s</emu-nt>' % (opt_lhs_nt_attrs, maybe_link_to_nt(lhs_nt, namespace), opt_mods)
            +
            '<emu-geq>%s</emu-geq>' % colons
            +
            '{RHSS}'
            +
            '</emu-production>'
        )

        if 'oneof' in prodn_attrs:
            rhss = (
                '<emu-oneof>one of</emu-oneof>'
                +
                '<emu-rhs>'
                +
                ''.join(
                    expand_symbol(symbol, namespace)
                    for line in post.split('\n')
                    for symbol in emu_grammars.rhs_tokenizer.tokenize(line)
                )
                +
                '</emu-rhs>'
            )

        else:
            rhss = []
            for rhs in post.split('\n'):
                if rhs == '': continue
                (rhs_text, rhs_id) = expand_rhs(rhs, namespace)
                rhss.append(rhs_text)
                if rhs_id:
                    _prod1_for_rhs_id_[(lhs_nt, rhs_id)] = production_template.replace('{RHSS}', rhs_text)

            rhss = '\n    '.join(rhss)

        production_element = production_template.replace('{RHSS}', rhss + '\n')

        if namespace == '' and emu_grammar_type == 'definition':
            if lhs_nt in _annexA_production_for_:
                assert lhs_nt == 'DoubleStringCharacter' # in JSON.parse
                stderr('multiple def prodns:', lhs_nt)
            else:
                _annexA_production_for_[lhs_nt] = production_element

        result += (
            ('\n' if pi > 0 else '')
            +
            production_element
        )

#                (r'\b([A-Z]\w*)\b', r'<emu-nt><a href="#prod-\1">\1</a></emu-nt>'),
#                (r'`(\w+)`',        r'<emu-t>\1</emu-t>'),

    return result

def expand_rhs(rhs, namespace):
    rhs = ( rhs
        .replace('&lt;', '<')
        .replace('&gt;', '>')
        .replace('&ldquo;', u'\u201C')
        .replace('&rdquo;', u'\u201D')
    )

    rhs_id = None
    rhs_content = ''
    rhs_attrs = ''
    for rthing in emu_grammars.rhs_tokenizer.tokenize(rhs):
        if type(rthing) == emu_grammars.A_id:
            # remember it and return it
            rhs_id = rthing.i
            continue

        elif type(rthing) == emu_grammars.A_guard:
            arg = rthing.s + rthing.n
            rhs_attrs = ' constraints="%s"' % arg
            x = '<emu-constraints>[%s]</emu-constraints>' % arg

        elif type(rthing) == emu_grammars.A_no_LT:
            x = '<emu-gann>[no <emu-nt><a href="#prod-LineTerminator">LineTerminator</a></emu-nt> here]</emu-gann>'

        elif type(rthing) == emu_grammars.A_empty:
            x = '<emu-gann>[empty]</emu-gann>'

        elif type(rthing) == emu_grammars.A_but_only_if:
            x = '<emu-gmod>but only if %s</emu-gmod>' % rthing.c.replace('>', '&gt;').replace('&le;', '≤')
            # and expand some emd spans

        elif type(rthing) == emu_grammars.A_but_not:
            assert len(rthing.b) > 0
            if len(rthing.b) == 1:
                [but] = rthing.b
                s = expand_symbol(but, namespace)
            else:
                s = 'one of ' + ' or '.join(
                        expand_symbol(but, namespace)
                        for but in rthing.b
                    )

            x = '<emu-gmod>but not %s</emu-gmod>' % s

        elif type(rthing) == emu_grammars.LAI:
            x = '<emu-gann>[lookahead = %s]</emu-gann>' % ''.join(
                expand_symbol(symbol, namespace)
                for symbol in rthing.ts
            )

        elif type(rthing) == emu_grammars.LAX:
            assert len(rthing.ts) > 0
            if len(rthing.ts) == 1:
                [symbol] = rthing.ts
                y = expand_symbol(symbol, namespace)
                if type(symbol) == emu_grammars.GNT:
                    operator = '∉'
                else:
                    operator = '≠'
            else:
                operator = '∉'
                y = '{ %s }' % ', '.join(
                    expand_symbol(term, namespace)
                    for term in rthing.ts
                )
            x = '<emu-gann>[lookahead %s %s]</emu-gann>' % (operator, y)

        else:
            x = expand_symbol(rthing, namespace)

        rhs_content += x

    return ('<emu-rhs%s>%s</emu-rhs>' % (rhs_attrs, rhs_content), rhs_id)

def expand_symbol(symbol, namespace):
    if type(symbol) == emu_grammars.T_lit:
        if symbol.c == 'async nLTh function':
            return '<emu-t>async</emu-t><emu-gann>[no <emu-nt><a href="#prod-LineTerminator">LineTerminator</a></emu-nt> here]</emu-gann><emu-t>function</emu-t>'
        else:
            return '<emu-t>%s</emu-t>' % symbol.c.replace('>', '&gt;').replace('<', '&lt;')

    elif type(symbol) == emu_grammars.T_nc:
        return '<emu-gprose>&lt;%s&gt;</emu-gprose>' % symbol.n

    elif type(symbol) == emu_grammars.T_u_p:
        if symbol.p is None:
            return '<emu-gprose>any Unicode code point</emu-gprose>'
        else:
            return '<emu-gprose>any Unicode code point with the Unicode property “%s”</emu-gprose>' % symbol.p

    elif type(symbol) == emu_grammars.T_u_r:
        return '<emu-gprose>%s through %s</emu-gprose>' % (symbol.lo, symbol.hi)

    elif type(symbol) == emu_grammars.GNT:
        nt_name = symbol.n
        emu_mods_content = ''

        if symbol.a:
            params = ', '.join(arg.s + arg.n for arg in symbol.a)
            maybe_params = ' params="%s"' % params
            emu_mods_content += '<emu-params>[%s]</emu-params>' % params
        else:
            maybe_params = ''

        maybe_optional = (' optional=""' if symbol.o else '')

        if symbol.o:
            emu_mods_content += '<emu-opt>opt</emu-opt>'

        maybe_link = maybe_link_to_nt(nt_name, namespace)

        if emu_mods_content:
            opt_emu_mods = '<emu-mods>' + emu_mods_content + '</emu-mods>'
        else:
            opt_emu_mods = ''

        return '<emu-nt%s%s>%s%s</emu-nt>' % (maybe_params, maybe_optional, maybe_link, opt_emu_mods)

    else:
        assert 0, symbol
        stderr(symbol)
        return repr(symbol)

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
