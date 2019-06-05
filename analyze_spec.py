#!/usr/bin/python3

# ecmaspeak-py/analyze_spec.py:
# Perform an initial static analysis of the spec.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, pdb
from collections import defaultdict, OrderedDict

import HTML, Section, emu_grammars
import shared
from shared import stderr, header, msg_at_posn, spec

def main():
    if len(sys.argv) != 3:
        stderr("usage: %s <output-dir> <spec.html>" % sys.argv[0])
        sys.exit(1)

    outdir = sys.argv[1]
    spec_path = sys.argv[2]

    shared.register_output_dir(outdir)

    # kludgey to assign to another module's global:
    shared.g_warnings_f = shared.open_for_output('warnings')

    spec.read_source_file(spec_path)

    spec.doc_node = HTML.parse_and_validate()

    # It feels like it would make more sense to check characters and indentation
    # before paring/checking markup, because they're more 'primitive' than markup.
    # But when it comes to fixing errors, you should make sure
    # you've got the markup correct before fiddling with indentation.
    # So to encourage that, have markup errors appear before indentation errors,
    # i.e. run the markup checks before indentation checks.
    # (Not sure about characters.)
    check_indentation()
    check_trailing_whitespace()
    check_characters()

    check_ids()

    check_tables()
    Section.make_and_check_sections()
    emu_grammars.do_stuff_with_grammars()
    collect_operation_info()
    check_sdo_coverage()

    spec.save()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def expand_imports(text):
    def repl_import(mo):
        (import_start, href, import_end) = mo.groups()
        t = open(href,'r').read()
        return import_start + t + import_end
    return re.sub(
        r'(<emu-import href="([^"]+)">)(</emu-import>)',
        repl_import,
        text
    )

def handle_insdel(text):

    # If a <del> element encloses all the non-whitespace content of a line,
    # delete the whole line.
    text = re.sub(r'\n *<del>[^<>]*</del> *(?=\n)', '', text)

    # Similarly of it encloses the body of an algorithm-step.
    text = re.sub(r'\n *1\. <del>.*</del>(?=\n)', '', text)
    # Insufficient to use "<del>[^<>]*</del>" because of steps with <emu-xref>
    # "<del>.*</del>" would fail if more than one <del> on a line,
    # but haven't seen that yet.

    # Otherwise, delete just the <del> element.
    text = re.sub(r'<del>.*?</del>', '', text)

    # And dissolve the <ins> </ins> tags.
    text = re.sub(r'</?ins>', '', text)

    return text

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_indentation():
    stderr("check_indentation...")
    header("checking indentation...")

    INDENT_UNIT = 2

    def check_indentation_for_node(node, expected_indent):
        if node.element_name == '#DOC':
            assert expected_indent is None
            for child in node.children:
                check_indentation_for_node(child, 0)
            return

        if node.element_name == '#LITERAL':
            # Mostly whitespace, but also:
            #     Editors:
            #     For each pair (_R_, _W_) ...
            #     For each element _eventsRecord_
            # whose indentation we don't care about?
            return

        def get_span_of_line_containing_posn(posn):
            # Excludes any newline at start or end.
            s = spec.text.rfind('\n', 0, posn)
            e = spec.text.find('\n', posn)
            return (
                0 if s == -1 else s+1,
                len(spec.text) if e == -1 else e
            )

        (start_line_s, start_line_e) = get_span_of_line_containing_posn(node.start_posn)
        (end_line_s,   end_line_e  ) = get_span_of_line_containing_posn(node.end_posn)

        def check_tag_indent(line_s, tag_s, element_name):
            portion_of_line_before_tag = spec.text[line_s : tag_s]
            if (
                portion_of_line_before_tag == ''
                or
                portion_of_line_before_tag.isspace()
            ):
                actual_indent = len(portion_of_line_before_tag)
                if actual_indent != expected_indent:
                    msg_at_posn(tag_s, f"expected indent={expected_indent}, got {actual_indent}")
            else:
                msg_at_posn(tag_s, f"{element_name} tag isn't the first non-blank thing on the line")

        # Check indentation of start tag.
        check_tag_indent(start_line_s, node.start_posn, node.element_name)

        start_tag_indent = node.start_posn - start_line_s

        if start_line_s == end_line_s:
            # This node begins and ends on a single line.
            # Therefore, all of its children (if any)
            # also begin and end on the same single line,
            # so no point looking at them.
            # And no point looking at the end tag (if any).
            return

        # This node covers more than one line.

        if node.element_name == '#COMMENT':
            # No children, no end-tag.
            # XXX We could look at the indentation of the text content,
            # but ...
            check_inline_content(node, start_tag_indent + INDENT_UNIT)
            return

        if node.element_name == 'pre' and len(node.children) == 1 and node.children[0].element_name == 'code':
            # These cases are always formatted like this:
            #     <pre><code>
            #       foo
            #     </code></pre>
            # which complicates things.
            code = node.children[0]
            assert code.attrs['class'] == 'javascript'
            check_inline_content(code, start_tag_indent + INDENT_UNIT)
            check_tag_indent(end_line_s, code.inner_end_posn, code.element_name)
            return

        if node.element_name in ['emu-grammar', 'emu-alg', 'emu-eqn']:
            # Indentation of content is checked elsewhere, as part of a more detailed check.
            # But check it here anyway.
            check_inline_content(node, start_tag_indent + INDENT_UNIT)

        elif not node.block_child_element_names:
            check_inline_content(node, start_tag_indent + INDENT_UNIT)

        else:
            # So recurse to its children.

            if node.element_name in ['thead', 'tbody']:
                # For obscure reasons, <tr> tags in spec.html
                # generally have the same indentation as
                # the surrounding <thead> and <tbody> tags.
                # If we didn't special-case them here,
                # they would cause a lot of warnings.
                #
                # However, we can't just say:
                #     child_expected_indent = start_tag_indent
                # because there are also a fair number of tables
                # where the <tr> tags *are* indented wrt <thead> and <tbody>.
                # And it would be impolite to complain when they're
                # adhering to the general rule re indenting.
                #
                # So we peek ahead at the indentation of the next line
                next_line_s = start_line_e + 1 # skip the newline character
                if spec.text[next_line_s : next_line_s+start_tag_indent+INDENT_UNIT].isspace():
                    # next line is indented wrt this line
                    child_expected_indent = start_tag_indent + INDENT_UNIT
                else:
                    child_expected_indent = start_tag_indent
            else:
                child_expected_indent = start_tag_indent + INDENT_UNIT

            for child in node.children:
                check_indentation_for_node(child, child_expected_indent)

        # ------------------------------
        # Check indentation of end tag.
        # 
        if node.element_name == 'p' and 'br' in node.inline_child_element_names:
            # Normally, a <p> element is all on one line.
            # But if it contains <br> elements,
            # we expect those to be either preceded or followed (or both) by newlines.
            inner_text = node.inner_source_text()
            if inner_text.startswith('\n'):
                # Expect:
                #    <p>
                #      xxx<br>
                #      yyy
                #    </p>
                pass
            else:
                # Expect:
                #    <p>xxx
                #      <br>
                #      yyy</p>
                # In this case, don't check the indentation of the end tag.
                return
        check_tag_indent(end_line_s, node.inner_end_posn, node.element_name)

    def check_inline_content(parent, expected_min_indent):
        if parent.element_name == '#COMMENT':
            isp = parent.start_posn + 4
            iep = parent.end_posn - 3
        else:
            isp = parent.inner_start_posn
            iep = parent.inner_end_posn

        line_ = [
            ( mo.end(1) - mo.start(1), mo.end(1) )
            for mo in re.compile(r'\n( *)\S').finditer(spec.text, isp, iep)
            # Note that the pattern ignores blank lines.
        ]

        def check_lines(lo, hi, emi):
            if lo == hi: return
            assert lo < hi
            (top_indent, x) = line_[lo]
            if top_indent != emi:
                msg_at_posn(x, f"expected indent={emi}, got {top_indent}")

            siblings = []
            for i in range(lo+1, hi):
                (indent, x) = line_[i]
                if indent < top_indent:
                    msg_at_posn(x, f"expected indent<{top_indent}, got {indent}")
                    siblings.append(i) # I guess
                elif indent == top_indent:
                    siblings.append(i)

            for (i,j) in zip([lo] + siblings, siblings + [hi]):
                check_lines(i+1, j, top_indent + INDENT_UNIT)

        check_lines(0, len(line_), expected_min_indent)

    check_indentation_for_node(spec.doc_node, None)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_trailing_whitespace():
    stderr("checking trailing whitespace...")
    header("checking trailing whitespace...")
    for mo in re.finditer(r'(?m)[ \t]+$', spec.text):
        posn = mo.start()
        msg_at_posn(posn, "trailing whitespace")

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_characters():
    stderr("checking characters...")
    header("checking characters...")
    for mo in re.finditer(r'[^\n -~]', spec.text):
        posn = mo.start()
        character = spec.text[posn]
        if character in ascii_replacement:
            suggestion = ": maybe change to %s" % ascii_replacement[character]
        else:
            suggestion = ''
        msg_at_posn(posn, "non-ASCII character U+%04x%s" %
            (ord(character), suggestion) )

ascii_replacement = {
    '\u00ae': '&reg;',    # REGISTERED SIGN
    '\u00ab': '&laquo;',  # LEFT-POINTING DOUBLE ANGLE QUOTATION MARK
    '\u00bb': '&raquo;',  # RIGHT-POINTING DOUBLE ANGLE QUOTATION MARK
    '\u2019': "'",        # RIGHT SINGLE QUOTATION MARK
    '\u2026': '&hellip;', # HORIZONTAL ELLIPSIS
    '\u2265': '&ge;',     # GREATER-THAN OR EQUAL TO
}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_ids():
    header("checking ids...")

    node_with_id_ = OrderedDict()

    def gather_def_ids(node):
        if 'id' in node.attrs:
            defid = node.attrs['id']

            id_prefix_expectation = {
              'emu-intro' : 'sec-',
              'emu-clause': 'sec-',
              'emu-annex' : 'sec-',
              'emu-eqn'   : 'eqn-',
              'emu-figure': 'figure-',
              'emu-table' : 'table-',
            }.get(node.element_name, None)
            if id_prefix_expectation:
                if not defid.startswith(id_prefix_expectation):
                    msg_at_posn(node.start_posn, f'for <{node.element_name} id="{defid}">, expected its id to start with "{id_prefix_expectation}"')
            else:
                if (False
                    or defid.startswith('sec-')
                    or defid.startswith('eqn-')
                    or defid.startswith('figure-')
                    or defid.startswith('table-')
                ):
                    msg_at_posn(node.start_posn, f'for <{node.element_name} id="{defid}">, did not expect its id to start that way')

            if defid in node_with_id_:
                msg_at_posn(node.start_posn, f"duplicate id: '{defid}'")

            node_with_id_[defid] = node

        for child in node.children:
            gather_def_ids(child)
    
    gather_def_ids(spec.doc_node)

    # -------------------------------------------------------------

    refids = set()

    def check_ref_ids(refnode):
        if refnode.element_name == 'emu-xref':
            if 'href' not in refnode.attrs:
                stderr("At", shared.convert_posn_to_linecol(refnode.start_posn))
                stderr("emu-xref element doesn't have an 'href' attribute")
                stderr("aborting")
                sys.exit()
            href = refnode.attrs['href']
            assert href.startswith('#')
            refid = href[1:]
            refids.add(refid)

            if refid in node_with_id_:

                defnode = node_with_id_[refid]
                if defnode.element_name in ['emu-clause', 'emu-annex', 'emu-table']:
                    pass
                elif defnode.element_name == 'dfn':
                    deftext = defnode.inner_source_text()
                    reftext = refnode.inner_source_text()
                    assert deftext != ''
                    if reftext != '' and reftext.lower() != deftext.lower():
                        # Auto-linking would fail to make `reftext` into a link?
                        # So we have to use an emu-xref?
                        pass
                    else:
                        msg_at_posn(refnode.start_posn, f"emu-xref used when auto-linking would work: '{refid}'")
                else:
                    msg_at_posn(defnode.start_posn, f"unexpected defnode element-name <{defnode.element_name}>")

            else:
                if refid in [
                    'table-binary-unicode-properties',
                    'table-nonbinary-unicode-properties',
                    'table-unicode-general-category-values',
                    'table-unicode-script-values',
                ]:
                    # Those ids are declared in emu-imported files.
                    pass

                elif refid in [
                    'prod-annexB-LegacyOctalEscapeSequence',
                    'prod-annexB-LegacyOctalIntegerLiteral',
                    'prod-annexB-NonOctalDecimalIntegerLiteral',
                ]:
                    # These don't exist in the source file,
                    # but are generated during the rendering process?
                    pass

                else:
                    msg_at_posn(refnode.start_posn, f"emu-xref refers to nonexistent id: {refid}")

        for child in refnode.children:
            check_ref_ids(child)
    
    check_ref_ids(spec.doc_node)

    # -------------------------------------------------------------

    for (id, defnode) in node_with_id_.items():
        if id in refids: continue

        # `id` was not referenced.

        if id in ['metadata-block', 'ecma-logo']:
            # Actually, it *is* referenced, but from the CSS.
            continue

        if defnode.element_name in ['emu-intro', 'emu-clause', 'emu-annex']:
            # It's okay if the id isn't referenced:
            # it's more there for the ToC and for inbound URLs.
            continue

        if defnode.element_name in ['emu-figure', 'emu-table']:
            # The text might refer to it as "the following figure/table",
            # so don't expect an exolicit reference to the id.
            # So you could ask, why bother giving an id then?
            # I suppose for inbound URLs, and consistency?
            continue

        if defnode.element_name in ['dfn', 'emu-eqn']:
            # It's likely that the rendering process will create references
            # to this id.
            continue

        msg_at_posn(defnode.start_posn, f"id declared but not referenced: '{id}'")

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_tables():
    stderr('check_tables...')
    header("checking tables...")
    for et in spec.doc_node.each_descendant_named('emu-table'):
        a_caption = et.attrs.get('caption', None)
        caption_children = [c for c in et.each_child_named('emu-caption')]
        if len(caption_children) == 0:
            e_caption = None
        elif len(caption_children) == 1:
            [emu_caption] = caption_children
            e_caption = emu_caption.inner_source_text().strip()
        else:
            assert 0
        # ----
        if a_caption and not e_caption:
            caption = a_caption
        elif e_caption and not a_caption:
            caption = e_caption
        else:
            assert 0, (a_caption, e_caption)

        if 'id' not in et.attrs:
            msg_at_posn(et.start_posn, f'no id attribute for table with caption "{caption}"')

        header_tr = [tr for tr in et.each_descendant_named('tr')][0]
        header_line = '; '.join(th.inner_source_text().strip() for th in header_tr.each_descendant_named('th'))
        if 'Field' in caption:
            # print(header_line, ':', caption)
            if re.match(r'^(.+) Fields$', caption):
                pass
            elif re.match(r'^Additional Fields of (.+)$', caption):
                pass
            else:
                assert 0, caption

        elif 'Slot' in caption:
            if re.match(r'^Internal Slots of (.+)$', caption):
                pass
            else:
                assert 0

        elif 'Method' in caption:
            if 'Internal Methods' in caption:
                assert caption in ['Essential Internal Methods', 'Additional Essential Internal Methods of Function Objects']
                assert header_line == 'Internal Method; Signature; Description'
            elif 'Records' in caption:
                assert re.fullmatch(r'(Additional )?(Abstract )?Methods of .+ Records', caption), caption
                assert header_line == 'Method; Purpose'
            elif caption == 'Proxy Handler Methods':
                assert header_line == 'Internal Method; Handler Method'
            else:
                assert 0

        elif 'Properties' in caption:
            assert re.fullmatch(r'<i>\w+</i> Interface( (Required|Optional))? Properties', caption)
            assert header_line == 'Property; Value; Requirements'

        else:
            # print('>>>', header_line, '---', caption)
            pass

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def collect_operation_info():
    stderr('collect_operation_info...')

    global info_for_op_named_
    info_for_op_named_ = {}

    for section in spec.doc_node.each_descendant_that_is_a_section():
        collect_operation_info_for_section(section)

# ------------------------------------------------------------------------------

def collect_operation_info_for_section(section):

    # cen = "child element names"
    cen_list = [
        c.element_name
        for c in section.block_children
    ]
    cen_str = ' '.join(cen_list)
    cen_set = set(cen_list)

    # XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

    if section.section_kind == 'syntax_directed_operation':

        # XXX: See define_ops_from_sdo_section() in static_type_analysis.py
        # Merge them somehow?

        if section.section_num.startswith('B.'):
            # Taking Annex B into account is difficult,
            # because it modifies the main-body grammar,
            # so RHS-indexes aren't always the same.
            # XXX For now, just skip it.
            return

        if section.section_title == 'Static Semantics: HasCallInTailPosition':
            assert len(section.block_children) == 2
            assert section.block_children[0].element_name == 'p'
            assert section.block_children[1].element_name == 'emu-note'
            assert len(section.section_children) == 2
            return
        elif section.section_title in ['Statement Rules', 'Expression Rules']:
            assert section.parent.section_title == 'Static Semantics: HasCallInTailPosition'
            sdo_name = 'HasCallInTailPosition'

        elif section.section_title == 'Static Semantics: TV and TRV':
            # Each rule specifies which SDO(section) it pertains to.
            sdo_name = None

        elif section.parent.section_title == 'Pattern Semantics':
            sdo_name = 'regexp-Evaluate'

        else:
            mo = re.fullmatch('(Static|Runtime) Semantics: (\w+)', section.section_title)
            assert mo, section.section_title
            sdo_name = mo.group(2)

        # ------------------------------------------------------------------------------

        if section.section_title == 'Static Semantics: NumberValueNotEverReferenced':
            # In the BigInt proposal, it has a <ul> defining "significant digit" and then <p> instead of <emu-alg>.
            assert cen_list == ['p', 'ul', 'emu-grammar', 'p', 'emu-grammar', 'p']
            return
        elif section.section_title == 'Static Semantics: BigIntValueNotEverReferenced':
            # In the BigInt proposal, it has <ul> instead of <emu-alg>
            assert cen_list == ['emu-grammar', 'ul', 'emu-grammar', 'ul']
            return

        if 'emu-grammar' in cen_set:
            if section.section_title == 'Static Semantics: NumericValue':
                # In the BigInt proposal, it has a <ul> defining "significant digit"
                assert cen_set == {'emu-grammar', 'emu-alg', 'ul', 'p'}
            else:
                assert cen_set <= set(['emu-grammar', 'emu-alg', 'emu-note', 'emu-see-also-para', 'emu-table', 'p'])
            # Each <emu-grammar> + <emu-alg> pair in an SDO unit.

            for (i,c) in enumerate(section.block_children):
                if c.element_name == 'emu-grammar':
                    next_c = section.block_children[i+1]
                    assert next_c.element_name in ['emu-alg', 'p']
                    if next_c.element_name == 'p':
                        assert next_c.inner_source_text().startswith('Is evaluated in exactly the same manner as')
                    op_add_defn('SDO', sdo_name, c, next_c)

        elif 'ul' in cen_set:
            assert cen_set <= set(['ul', 'p', 'emu-table', 'emu-note'])
            # Each <li> in the <ul> is an "inline SDO".

            for ul in section.block_children:
                if ul.element_name != 'ul': continue
                for li in ul.children:
                    if li.element_name != 'li': continue

                    li_ist = li.inner_source_text().strip()
                    if re.match(r'it is not `0`|there is a nonzero digit', li_ist):
                        # This is the <ul> at the end of 
                        # 7.1.3.1.1 Runtime Semantics: MV
                        # and
                        # 11.8.3.1 Static Semantics: MV
                        # We're not interested in it.
                        # print(section.section_num, section.section_title, section.section_id)
                        continue

                    if li_ist == 'The TRV of a |HexDigit| is the SV of the |SourceCharacter| that is that |HexDigit|.':
                        # XXX not sure how to handle this yet. For now, ignore it.
                        continue

                    (emu_grammars, text) = extract_grammars(li)

                    assert emu_grammars

                    if re.fullmatch(r'The TV and TRV of <G> is .+', text):
                        sdo_names = ['TV', 'TRV']
                    else:
                        mo = re.fullmatch(r'The (\w+) of <G>( or of <G>)* is .+', text)
                        assert mo
                        sdo_names = [mo.group(1)]

                    # The part of the <li> after the "is" isn't marked off at all,
                    # so there isn't an HNode to supply as the definition.
                    # Instead, use the li itself?
                    # XXX Or does that argue that this stuff should be done after parse_pseudocode?

                    for sdo_name in sdo_names:
                        for emu_grammar in emu_grammars:
                            op_add_defn('SDO', sdo_name, emu_grammar, li)

        elif 'emu-alg' in cen_set:
            assert cen_set <= set(['emu-alg', 'p', 'emu-note'])
            # Each <p> + <emu-alg> pair is an SDO unit.
            assert sdo_name in ['Evaluation', 'regexp-Evaluate']

            # print(cen_str)
            for (i,c) in enumerate(section.block_children):
                if c.element_name == 'p':
                    (emu_grammars, text) = extract_grammars(c)

                    if len(emu_grammars) == 0:
                        assert text == 'With parameter _direction_.'
                        # ignore it
                        continue

                    assert len(emu_grammars) == 1
                    [emu_grammar] = emu_grammars

                    if text == 'The production <G>, where @ is one of the bitwise operators in the productions above, is evaluated as follows:':
                        assert emu_grammar.attrs.get('type', 'reference') == 'example'
                        assert emu_grammar.inner_source_text() == 'A : A @ B'
                        # XXX skip it?

                    elif text in [
                        'The production <G> evaluates by returning the CharSet containing all Unicode code points included in the CharSet returned by |UnicodePropertyValueExpression|.',
                        'The production <G> evaluates by returning the CharSet containing all Unicode code points not included in the CharSet returned by |UnicodePropertyValueExpression|.',
                    ]:
                        op_add_defn('SDO', sdo_name, emu_grammar, None)

                    elif text == 'The production <G> evaluates as follows:':
                        emu_alg = section.block_children[i+1]
                        assert emu_alg.element_name == 'emu-alg'
                        op_add_defn('SDO', sdo_name, emu_grammar, emu_alg)

                    else:
                        assert 0, text

        else:
            print(section.section_num, section.section_title, section.section_id)
            print(cen_str)
            assert 0

    # XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

    # elif section.section_kind == 'something else': ...

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def extract_grammars(x):
    emu_grammars = []
    text = ''
    for c in x.children:
        if c.element_name == 'emu-grammar':
            emu_grammars.append(c)
            text += '<G>'
        else:
            text += c.source_text()
    return (emu_grammars, text.strip())

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Operation:
    def __init__(self, name, kind):
        self.name = name
        self.kind = kind
        self.definitions = []

def op_add_defn(op_kind, op_name, emu_grammar, emu_alg):
    assert type(op_name) == str
    assert emu_grammar.element_name == 'emu-grammar'

    if op_name in info_for_op_named_:
        op_info = info_for_op_named_[op_name]
        assert op_info.kind == op_kind
    else:
        op_info = Operation(op_name, op_kind)
        info_for_op_named_[op_name] = op_info

    op_info.definitions.append( (emu_grammar, emu_alg) )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_sdo_coverage():
    stderr('check_sdo_coverage...')
    global sdo_coverage_map
    sdo_coverage_map = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))

    # collect sdo_coverage_info:
    for (op_name, op_info) in info_for_op_named_.items():
        if op_info.kind == 'SDO':
            for (emu_grammar, emu_alg) in op_info.definitions:
                for (lhs_nt, def_i, optionals) in emu_grammar.summary:
                    sdo_coverage_map[op_name][lhs_nt][def_i].append(optionals)

    analyze_sdo_coverage_info()

# ------------------------------------------------------------------------------

def analyze_sdo_coverage_info():
    coverage_f = shared.open_for_output('sdo_coverage')
    def put(*args): print(*args, file=coverage_f)

    for (sdo_name, coverage_info_for_this_sdo) in sorted(sdo_coverage_map.items()):

        if sdo_name == 'Contains':
            # XXX can we do anything useful here?
            # we could check for conflicting defs
            continue

        nt_queue = sorted(coverage_info_for_this_sdo.keys())
        def queue_ensure(nt):
            if nt not in nt_queue: nt_queue.append(nt)

        for lhs_nt in nt_queue:
            # print('    ', lhs_nt)

            nt_info = emu_grammars.info_for_nt_[lhs_nt]
            assert 'A' in nt_info.def_occs
            (_, _, def_rhss) = nt_info.def_occs['A']

            for (def_i, def_rhs) in enumerate(def_rhss):
                GNTs = [r for r in def_rhs if r.T == 'GNT']
                oGNTs = [gnt for gnt in GNTs if gnt.o]
                nGNTs = [gnt for gnt in GNTs if not gnt.o]

                for opt_combo in each_opt_combo(oGNTs):
                    opt_combo_str = ''.join(omreq[0] for (nt, omreq) in opt_combo)
                    rules = sdo_rules_that_handle(sdo_name, lhs_nt, def_i, opt_combo)
                    if len(rules) == 1:
                        # great
                        pass
                    elif len(rules) > 1:
                        put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} {opt_combo_str} is handled by {len(rules)} rules!")
                    elif is_sdo_coverage_exception(sdo_name, lhs_nt, def_i):
                        # okay
                        pass
                    else:
                        nts = [gnt.n for gnt in nGNTs] + required_nts_in(opt_combo)
                        if len(nts) == 1:
                            # The rule for chain productions applies.
                            # So recurse on the rhs non-terminal.
                            [nt] = nts

                            # DEBUG:
                            # put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} chains to {nt}")
                            # That creates a lot of output, but it's really useful
                            # when you're trying to figure out why "needs a rule" messages appear.

                            queue_ensure(nt)
                        else:
                            put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} {opt_combo_str} needs a rule")

    coverage_f.close()

def each_opt_combo(oGNTs):
    N = len(oGNTs)
    if N == 0:
        yield []
    elif N == 1:
        [a] = oGNTs
        yield [(a.n, 'omitted' )]
        yield [(a.n, 'required')]
    elif N == 2:
        [a, b] = oGNTs
        yield [(a.n, 'omitted' ), (b.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'required')]
    elif N == 3:
        [a, b, c] = oGNTs
        yield [(a.n, 'omitted' ), (b.n, 'omitted' ), (c.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'omitted' ), (c.n, 'required')]
        yield [(a.n, 'omitted' ), (b.n, 'required'), (c.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'required'), (c.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'omitted' ), (c.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'omitted' ), (c.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'required'), (c.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'required'), (c.n, 'required')]
    else:
        assert 0

def required_nts_in(opt_combo):
    return [nt for (nt, omreq) in opt_combo if omreq == 'required']

def sdo_rules_that_handle(sdo_name, lhs_nt, def_i, opt_combo):
    coverage_info_for_this_sdo = sdo_coverage_map[sdo_name]
    coverage_info_for_this_nt = coverage_info_for_this_sdo[lhs_nt]
    if def_i not in coverage_info_for_this_nt: return []
    list_of_opt_covers = coverage_info_for_this_nt[def_i]
    covers = []
    for opt_cover in list_of_opt_covers:
        # print(opt_cover, covers_opt_combo(opt_cover, opt_combo))
        if covers_opt_combo(opt_cover, opt_combo):
            covers.append(opt_cover)
    return covers

def covers_opt_combo(opt_cover, opt_combo):
    assert len(opt_cover) == len(opt_combo)
    for (cover_item, combo_item) in zip(opt_cover, opt_combo):
        assert cover_item[0] == combo_item[0]
        assert cover_item[1] in ['omitted', 'required', 'either']
        assert combo_item[1] in ['omitted', 'required']
        if cover_item[1] == combo_item[1]:
            # easy
            pass
        elif cover_item[1] == 'either':
            # covers either
            pass
        else:
            # incompatible
            return False
    return True

def is_sdo_coverage_exception(sdo_name, lhs_nt, def_i):
    # Looking at the productions that share a LHS
    # (or equivalently, the RHSs of a multi-production),
    # it's typically the case that if an SDO can be invoked on one,
    # then it can be invoked on all.
    # And thus, if you see an SDO defined on one,
    # you should expect to see it defined on all,
    # either explicitly, or implicitly via chain productions.
    #
    # This function identifies exceptions to that rule of thumb.

    if sdo_name == 'CharacterValue' and lhs_nt == 'ClassEscape' and def_i == 2:
        # Invocations of this SDO on ClassAtom and ClassAtomNoDash
        # are guarded by `IsCharacterClass ... is *false*`.
        # This excludes the `ClassEscape :: CharacterClassEscape` production.
        return True

    if (
        sdo_name == 'CoveredParenthesizedExpression'
        and
        lhs_nt == 'CoverParenthesizedExpressionAndArrowParameterList'
        and
        def_i != 0
    ):
        # For this SDO, we're guaranteed (by early error) that rhs must be def_i == 0,
        # so the SDO doesn't need to be defined for def_i != 0.
        return True

    if sdo_name == 'DefineMethod' and lhs_nt == 'MethodDefinition' and def_i != 0:
        # "Early Error rules ensure that there is only one method definition named `"constructor"`
        # and that it is not an accessor property or generator definition."
        # (or AsyncMethod)
        # See SpecialMethod.
        return True

    if sdo_name == 'Evaluation' and lhs_nt == 'ClassDeclaration' and def_i == 1:
        # "ClassDeclaration : `class` ClassTail</emu-grammar>
        # only occurs as part of an |ExportDeclaration| and is never directly evaluated."
        return True

    if sdo_name == 'HasName':
        # Invocations of this SDO are guarded by `IsFunctionDefinition of _expr_ is *true*`,
        # so the SDO doesn't need to be defined for most kinds of expr.
        # Assume that it's defined for all that need it.
        return True

    if sdo_name == 'NamedEvaluation':
        # NamedEvaluation is invoked on |Initializer| and |AssignmentExpression|,
        # which are fairly general, except that it's only invoked on nodes
        # for which IsAnonymousFunctionDefinition() is true,
        # which implies that IsFunctionDefition is true and HasName is false.
        # return lhs_nt not in [
        #     'ArrowFunction',
        #     'AsyncArrowFunction',
        #     'FunctionExpression',
        #     'GeneratorExpression',
        #     'AsyncGeneratorExpression',
        #     'ClassExpression',
        #     'AsyncFunctionExpression',
        # ]
        # As above, assume it's defined for all that need it.
        return True

    if sdo_name == 'IsConstantDeclaration' and lhs_nt == 'ExportDeclaration' and def_i in [0,1,2,3]:
        # LexicallyScopedDeclarations skips these, so IsConstantDeclaration won't be invoked on them.
        return True

    if (
        sdo_name in ['PropName', 'PropertyDefinitionEvaluation']
        and 
        lhs_nt == 'PropertyDefinition'
        and
        def_i == 1
    ):
        # "Use of |CoverInitializedName| results in an early Syntax Error in normal contexts..."
        return True

    # ----------

    if (
        sdo_name == 'Evaluation'
        and
        lhs_nt in [
            'BitwiseANDExpression',
            'BitwiseXORExpression',
            'BitwiseORExpression',
        ]
        and
        def_i == 1
    ):
        # This is handled by the stupid "A : A @ B" rule.
        return True

    return False

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

if 1:
    main()
else:
    import cProfile
    cProfile.run('main()', '_prof')
    # python3 -m pstats
    # read _prof
    # sort time
    # stats 10

# vim: sw=4 ts=4 expandtab columns=86
