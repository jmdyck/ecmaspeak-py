#!/usr/bin/python3

# ecmaspeak-py/analyze_spec.py:
# Perform an initial static analysis of the spec.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, pdb
from collections import defaultdict, OrderedDict

import HTML, Section, emu_grammars, Pseudocode
import shared
from shared import stderr, msg_at_node, msg_at_posn, spec
from emu_tables import analyze_table
import intrinsics
from intrinsics import check_references_to_intrinsics, process_intrinsics_facts
import records
import Pseudocode

def main():
    if len(sys.argv) != 3:
        stderr("usage: %s <output-dir> <spec.html>" % sys.argv[0])
        sys.exit(1)

    outdir = sys.argv[1]
    spec_path = sys.argv[2]

    shared.register_output_dir(outdir)

    shared.msg_at_posn_start()

    spec.read_source_file(spec_path)

    spec.doc_node = HTML.parse_and_validate()

    # Now that errors/warnings are interleaved with a copy of the spec text,
    # the order in which we call these functions
    # only matters when two msg_at_posn() calls
    # address the exact same position.

    check_characters()

    check_indentation()
    check_trailing_whitespace()
    check_for_extra_blank_lines()

    check_ids()
    check_dfns()

    Pseudocode.create_all_parsers()

    check_tables()
    records.extract_record_schemas()
    Section.make_and_check_sections()
    records.print_schema_hierarchies()
    process_intrinsics_facts()
    check_references_to_intrinsics()
    grammar_success = emu_grammars.do_stuff_with_emu_grammars()
    if grammar_success:
        Pseudocode.do_stuff_with_pseudocode()

    check_globals()

    shared.msg_at_posn_finish()

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

            if node.element_name in ['html', 'head', 'body']:
                # PR #2067 added <html>, <head> and <body> tags
                # and (reasonably) didn't re-indent everything else.
                child_expected_indent = start_tag_indent

            elif node.element_name in ['thead', 'tbody']:
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

def check_for_extra_blank_lines():
    stderr("checking for extra blank lines...")
    for mo in re.finditer(r'\n( *\n){2,}', spec.text):
        posn = mo.end() - 1
        msg_at_posn(posn, "2 or more adjacent blank lines")

    for mo in re.finditer(r'\n( *\n *</emu-clause>)', spec.text):
        posn = mo.start(1)
        msg_at_posn(posn, "blank line before end-clause tag")

def check_trailing_whitespace():
    stderr("checking trailing whitespace...")
    for mo in re.finditer(r'(?m)[ \t]+$', spec.text):
        posn = mo.start()
        msg_at_posn(posn, "trailing whitespace")

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_characters():
    stderr("checking characters...")
    pattern = r'''(?x)[^
        \n    # newline
        \x20  # space
        !-~   # printable ASCII chars

        « # U+000ab (&laquo;)
        » # U+000bb (&raquo;)
        × # U+000d7 (&times;)
        π # U+003c0 (&pi;)
        — # U+02014 (&mdash;)
        “ # U+0201c (&ldquo;)
        ” # U+0201d (&rdquo;)
        … # U+02026 (&hellip;)
        ℝ # U+0211d (DOUBLE-STRUCK CAPITAL R) {fancy_r}
        ℤ # U+02124 (DOUBLE-STRUCK CAPITAL Z) {fancy_z}
        → # U+02192 (&rarr;)
        ∞ # U+0221e (&infin;)
        ≠ # U+02260 (&ne;)
        ≤ # U+02264 (&le;)
        ≥ # U+02265 (&ge;)
        𝔽 # U+1d53d (DOUBLE-STRUCK CAPITAL F) {fancy_f}
    ]'''
    for mo in re.finditer(pattern, spec.text):
        # Note that this will (among other things) find and complain about TAB characters.
        posn = mo.start()
        character = spec.text[posn]
        msg_at_posn(posn, "unusual character U+%04x" % ord(character))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_ids():
    stderr("checking ids...")

    node_with_id_ = OrderedDict()
    all_oldids = set()

    def gather_def_ids(node):
        if 'id' in node.attrs:
            defid = node.attrs['id']

            # ----------
            # no duplicate ids, of course

            if defid in node_with_id_:
                msg_at_node(node, f"duplicate id: '{defid}'")

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
                    msg_at_node(node, f'Expected the id to start with "{id_prefix_expectation}"')
            else:
                if (False
                    or defid.startswith('sec-')
                    or defid.startswith('eqn-')
                    or defid.startswith('figure-')
                    or defid.startswith('table-')
                ):
                    msg_at_node(node, f'Did not expect the id to start that way')

            # ----------
            # If an element defines an abstract operation,
            # its id should be ...

            if 'aoid' in node.attrs:
                # TODO: After the merge of #545, most abstract ops don't have an 'aoid' attribute;
                # instead it's generated at 'render' time.
                # (But a few things do still have an 'aoid' attribute, so this code is still being executed,
                # just not as much as we want.)
                aoid = node.attrs['aoid']
                assert node.element_name in ['emu-clause', 'emu-eqn']
                assert id_prefix_expectation is not None
                possibles = [
                    id_prefix_expectation + aoid.lower().replace(' ', '-').replace('::', '-'),
                    id_prefix_expectation + aoid,
                    id_prefix_expectation + kebab(aoid),
                    id_prefix_expectation + 'static-semantics-' + aoid.lower(),
                    id_prefix_expectation + 'runtime-semantics-' + aoid.lower(),
                ]
                if defid not in possibles:
                    msg_at_node(node, f'Expected id="{possibles[0]}"')

        if node.element_name == 'emu-alg':
            for mo in re.finditer(r'\bid="([^"]+)"', node.inner_source_text()):
                defid = mo.group(1)

                # ----------
                # no duplicate ids

                if defid in node_with_id_:
                    msg_at_node(node, f"duplicate id: '{defid}'")

                node_with_id_[defid] = node
                # XXX Should really be the node that will later be constructed
                # for the step in which this step_attribute occurs.

                # ----------
                # id should begin with "step-"

                assert defid.startswith('step-')

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
                if defnode.element_name in ['emu-clause', 'emu-annex', 'emu-table', 'emu-alg', 'emu-note']:
                    pass
                elif defnode.element_name == 'dfn':
                    deftext = defnode.inner_source_text()
                    reftext = refnode.inner_source_text()
                    assert deftext != ''
                    if reftext == '':
                        # <emu-xref href="#{refid}"></emu-xref>
                        msg_at_node(
                            refnode,
                            f"Unnecessary emu-xref element: replace it with '{deftext}' and that will auto-link to '{refid}'"
                        )
                    else:
                        # <emu-xref href="#{refid}">{reftext}</emu-xref>
                        variants = defnode.attrs.get('variants', '').split(',')
                        if reftext == deftext or reftext in variants:
                            msg_at_node(
                                refnode,
                                f"Unnecessary emu-xref element: delete tags and '{reftext}' will auto-link to '{refid}'"
                            )
                else:
                    msg_at_node(defnode, f"unexpected defnode element-name <{defnode.element_name}>")

            else:
                if refid in [
                    'table-binary-unicode-properties',
                    'table-nonbinary-unicode-properties',
                    'table-binary-unicode-properties-of-strings',
                    'table-unicode-general-category-values',
                    'table-unicode-script-values',
                ]:
                    # Those ids are declared in emu-imported files.
                    pass

                else:
                    msg_at_node(refnode, f"emu-xref refers to nonexistent id: {refid}")

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

        msg_at_node(defnode, f"id declared but not referenced: '{id}'")

    spec.node_with_id_ = node_with_id_

def kebab(id):
    def replfunc(mo):
        low = mo.group(0).lower()
        if mo.start() == 0:
            return low
        else:
            return '-' + low
    return re.sub('[A-Z]', replfunc, id)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_dfns():
    stderr('check_dfns...')

    spec.dfn_for_term_ = {}
    for dfn in spec.doc_node.each_descendant_named('dfn'):
        ist = dfn.inner_source_text()
        assert ist not in spec.dfn_for_term_
        spec.dfn_for_term_[ist] = dfn

        variants = dfn.attrs.get('variants')
        if variants:
            variants = variants.split(',')
            for variant in variants:
                assert variant not in spec.dfn_for_term_
                spec.dfn_for_term_[variant] = dfn

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_tables():
    stderr('check_tables...')
    for et in spec.doc_node.each_descendant_named('emu-table'):
        analyze_table(et)

        caption = et._caption
        header_line = '; '.join(et._header_row.cell_texts)

        def check_value_descriptions_in_column(col_index):
            for row in et._data_rows:
                col_name = et._header_row.cell_texts[col_index]
                cell_value = row.cell_texts[col_index]
                Pseudocode.parse(row.cell_nodes[col_index], 'field_value_type')

        if 'Field' in caption or ('Method' in caption and 'Record' in caption):
            # See records.process_tables()
            pass

        elif 'Slot' in caption:
            if re.match(r'^Internal Slots of (.+)$', caption):
                if header_line == 'Internal Slot; Type; Description':
                    check_value_descriptions_in_column(1)
                else:
                    assert 0, header_line
            else:
                assert 0

        elif 'Method' in caption:
            if 'Internal Methods' in caption:
                assert caption in ['Essential Internal Methods', 'Additional Essential Internal Methods of Function Objects']
                assert header_line == 'Internal Method; Signature; Description'
            elif caption == 'Proxy Handler Methods':
                assert header_line == 'Internal Method; Handler Method'
            else:
                assert 0

        elif 'Properties' in caption:
            assert re.fullmatch(r'[\w ]+ Interface( (Required|Optional))? Properties', caption)
            assert header_line == 'Property; Value; Requirements'
            check_value_descriptions_in_column(1)

        elif caption == 'Attributes of an Object property':
            assert header_line == 'Attribute Name; Types of property for which it is present; Value Domain; Default Value; Description'
            check_value_descriptions_in_column(2)

        elif 'Intrinsic Objects' in caption:
            # see Section.extract_intrinsic_info_from_WKI_section()
            # and intrinsics.each_row_in_wki_table()
            pass

        else:
            # print('>>>', header_line, '---', caption)
            pass

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_globals():
    stderr('check_globals...')
    global_object_property_names = set()

    sgo = spec.node_with_id_['sec-global-object']
    for section in sgo.each_descendant_that_is_a_section():
        if '_property' in section.section_kind:
            # print('>', section.section_kind, section.section_title)
            mo = re.fullmatch(r'(\w+)( \(.*\))?', section.section_title)
            assert mo
            global_property_name = mo.group(1)
            if section.parent.section_title != 'Value Properties of the Global Object':
                global_object_property_names.add(global_property_name)

    def show_names_set(label, names_set):
        for name in sorted(names_set):
            stderr(f"> {label}: {name}")
        
    show_names_set("In 'The Global Object' but not in WKI", global_object_property_names - intrinsics.global_property_names)
    show_names_set("In WKI but not in 'The Global Object'", intrinsics.global_property_names - global_object_property_names)

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

# vim: sw=4 ts=4 expandtab
