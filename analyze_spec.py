#!/usr/bin/python3

# ecmaspeak-py/analyze_spec.py:
# Perform an initial static analysis of the spec.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, pdb
from collections import defaultdict, OrderedDict

import HTML, Section, emu_grammars, Pseudocode
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
    check_intrinsics()
    Section.make_and_check_sections()
    emu_grammars.do_stuff_with_grammars()
    
    Pseudocode.do_stuff_with_pseudocode()

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
        if character == '\u211d':
            # PR 1135 introduced tons of these
            continue

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
    all_oldids = set()

    def gather_def_ids(node):
        if 'id' in node.attrs:
            defid = node.attrs['id']

            # ----------
            # no duplicate ids, of course

            if defid in node_with_id_:
                msg_at_posn(node.start_posn, f"duplicate id: '{defid}'")

            node_with_id_[defid] = node

            # ----------
            # id should begin with "(sec|eqn|figure|table)-"
            # if and only if the node is of certain kinds.

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

            # ----------
            # If an element defines an abstract operation,
            # its id should be ...

            if 'aoid' in node.attrs:
                aoid = node.attrs['aoid']
                assert node.element_name in ['emu-clause', 'emu-annex', 'emu-eqn', 'dfn']
                if id_prefix_expectation is None:
                    id_prefix_expectation = 'sec-' # for thisFooValue
                possibles = [
                    id_prefix_expectation + aoid.lower().replace(' ', '-').replace('::', '-'),
                    id_prefix_expectation + aoid,
                    id_prefix_expectation + kebab(aoid)
                ]
                if defid not in possibles:
                    msg_at_posn(node.start_posn, f'for <{node.element_name} id="{defid}" aoid={aoid}">, expected id="{possibles[0]}"')

        if 'oldids' in node.attrs:
            for oldid in node.attrs['oldids'].split(','):
                assert oldid not in all_oldids
                all_oldids.add(oldid)

        for child in node.children:
            gather_def_ids(child)
    
    gather_def_ids(spec.doc_node)

    # An id can't be both an oldid and a current id.
    assert not all_oldids & set(node_with_id_.keys())

    # Print a sorted list of all ids
    # (so that we notice if any ever go away):
    ids_f = shared.open_for_output('ids')
    for id in sorted(all_oldids | set(node_with_id_.keys())):
        print(id, file=ids_f)
    ids_f.close()

    # -------------------------------------------------------------

    # Find "referenced but not declared" ids.

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

    # Find "declared but nor referenced" ids.

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

def kebab(id):
    def replfunc(mo):
        low = mo.group(0).lower()
        if mo.start() == 0:
            return low
        else:
            return '-' + low
    return re.sub('[A-Z]', replfunc, id)

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
            elif caption == 'Fields of the Private Name':
                # PR 1668
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

        elif 'Intrinsic Objects' in caption:
            assert caption in [
                'Well-Known Intrinsic Objects',
                'Additional Well-known Intrinsic Objects',
            ]
            well_known_intrinsics_table_spans.append( (et.start_posn, et.end_posn) )
            
            new_names = {}
            assert header_line == 'Intrinsic Name; Global Name; ECMAScript Language Association'
            for tr in et.each_descendant_named('tr'):
                if tr == header_tr: continue
                [oname, global_name, assoc] = [
                    td.inner_source_text().strip()
                    for td in tr.each_descendant_named('td')
                ]

                assert re.fullmatch(r'%\w+%', oname)
                assert oname not in well_known_intrinsics

                assert re.fullmatch(r"|`\w+(\.\w+)*`", global_name)

                if ';' in assoc or 'i.e.' in assoc:
                    mo = re.search(r'; i.e., (%\w+(\.\w+)+%)$', assoc)
                    assert mo
                    new_name = mo.group(1)
                    assert new_name not in well_known_intrinsics
                    assert new_name not in new_names
                    new_names[new_name] = tr.start_posn

                    assert new_name != oname
                    well_known_intrinsics[oname] = f"old name;  2950,$s/{oname}/{new_name}/gc"
                    well_known_intrinsics[new_name] = "new name"
                else:
                    well_known_intrinsics[oname] = "only name"

            # Have to do this after processing the table,
            # because of possible forward references.
            # (E.g., on the row for %AsyncGenerator%,
            # column 3 mentions %AsyncGeneratorFunction.prototype%,
            # which implies the existence of %AsyncGeneratorFunction%,
            # which is declared in column 1 of the *next* row.)
            for (new_name, tr_posn) in new_names.items():
                base_of_new_name = re.sub(r'\..*', '%', new_name)
                if base_of_new_name not in well_known_intrinsics:
                    msg_at_posn(tr_posn, f"Implied intrinsic doesn't exist: {base_of_new_name}")

        else:
            # print('>>>', header_line, '---', caption)
            pass

well_known_intrinsics_table_spans = []
well_known_intrinsics = {}

def check_intrinsics():
    stderr("checking intrinsics...")
    header("checking intrinsics...")
    # We can't just scan through spec.text looking for %...%,
    # because that would find occurrences in element IDs,
    # which are lower-cased.
    # Instead, just look in literal (text) nodes.
    # (Note that this skips occurrences of "%<var>Foo</var>Prototype%".)
    for tnode in spec.doc_node.each_descendant_named('#LITERAL'):
        for mo in re.compile(r'%\S+%').finditer(spec.text, tnode.start_posn, tnode.end_posn):
            itext = mo.group(0)
            itext_start = mo.start(0)
            if itext in ['%name%', '%name.a.b%']:
                # placeholders
                continue
            if itext in ['%_NativeError_%', '%_TypedArray_%']:
                # metavariable interpolation
                continue

            is_in_table = any(
                table_start < itext_start < table_end
                for (table_start, table_end) in well_known_intrinsics_table_spans 
            )

            status = well_known_intrinsics.get(itext, "doesn't exist")
            if status == "doesn't exist":
                msg_at_posn(itext_start, f"Intrinsic doesn't exist: {itext}")
            elif status.startswith("old name"):
                if not is_in_table:
                    msg_at_posn(itext_start, f"Using {status}")

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
