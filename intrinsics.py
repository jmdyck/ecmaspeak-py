#!/usr/bin/python3

# ecmaspeak-py/intrinsics.py:
# Code that deals with intrinsic objects.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re

from shared import stderr, spec

# ------------------------------------------------------------------------------

well_known_intrinsics = {}

def handle_intrinsics_table(emu_table):
    assert emu_table._caption in [
        'Well-Known Intrinsic Objects',
        'Additional Well-known Intrinsic Objects',
    ]
    
    assert emu_table._header_row.cell_texts == ['Intrinsic Name', 'Global Name', 'ECMAScript Language Association']

    for row in emu_table._data_rows:
        [percent_name, global_name, assoc] = row.cell_texts

        assert re.fullmatch(r'%\w+%', percent_name)
        assert percent_name not in well_known_intrinsics
        well_known_intrinsics[percent_name] = True

        if global_name == '':
            pass
        else:
            assert re.fullmatch(r"`\w+`", global_name)
            assert global_name[1:-1] == percent_name[1:-1]

        if re.match(r'(A function|An) object that ', assoc):
            phrase = None
        elif (mo := re.fullmatch(r'The (.+) \(<emu-xref href="[^"]+"></emu-xref>\)', assoc)):
            phrase = 'the ' + mo.group(1)
        else:
            assert 0, assoc

def check_references_to_intrinsics():
    stderr("check_references_to_intrinsics...")

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

            base_intrinsic = re.sub(r'\.[^%]+', '', itext)

            if base_intrinsic not in well_known_intrinsics:
                msg_at_posn(itext_start, f"Intrinsic doesn't exist: {base_intrinsic}")

             # XXX We should also check that any ".foo.bar" appended to the base intrinsic
             # also makes sense, but we don't have the necessary info readily available.

# vim: sw=4 ts=4 expandtab
