#!/usr/bin/python3

# ecmaspeak-py/emu_table.py:
# Code for dealing with <emu-table> elements generically.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import typing, re
from dataclasses import dataclass

import HTML
from shared import msg_at_posn

# ------------------------------------------------------------------------------

def analyze_table(emu_table):
    # Do generic processing of the table,
    # to get its content into a more convenient data structure.

    assert emu_table.element_name == 'emu-table'

    # -----------------------------

    a_caption = emu_table.attrs.get('caption', None)
    caption_children = [c for c in emu_table.each_child_named('emu-caption')]
    if len(caption_children) == 0:
        e_caption = None
    elif len(caption_children) == 1:
        [emu_caption] = caption_children
        e_caption = emu_caption.inner_source_text().strip()
    else:
        assert 0

    if a_caption and not e_caption:
        caption = a_caption
    elif e_caption and not a_caption:
        caption = e_caption
    else:
        assert 0, (a_caption, e_caption)

    emu_table._caption = caption

    # -----------------------------

    if 'id' not in emu_table.attrs:
        msg_at_posn(emu_table.start_posn, f'no id attribute for table with caption "{caption}"')

    # -----------------------------

    emu_table._header_row = None
    emu_table._data_rows = []

    for tr in emu_table.each_descendant_named('tr'):
        assert not tr.attrs

        cell_nodes = []
        for tr_child in tr.children:
            if tr_child.is_whitespace():
                pass
            elif tr_child.element_name in ['th', 'td']:
                cell_nodes.append(tr_child)
            else:
                assert 0

        raw_cell_texts = []
        cooked_cell_texts = []
        for cell_node in cell_nodes:
            raw_cell_text = cell_node.inner_source_text().strip()
            cooked_cell_text = quasi_ecmarkdown(raw_cell_text)

            colspan = int(cell_node.attrs.get('colspan', '1'))
            if colspan != 1: assert emu_table._caption == 'Import Forms Mappings to ImportEntry Records'

            raw_cell_texts.extend([raw_cell_text] * colspan)
            cooked_cell_texts.extend([cooked_cell_text] * colspan)

        is_header = all(cell_node.element_name == 'th' for cell_node in cell_nodes)

        if is_header:
            # This is a header row.
            assert emu_table._header_row is None # Can't have more than one header row.
            assert emu_table._data_rows == [] # Can't have header row after data rows.
            as_dict = None
        else:
            # This is a data row.
            # Probably all cells are <td>,
            # but it also happens (in the Module evaluation examples)
            # that the first is <th> and the rest are <td>
            # (in which case, we treat the <th> the same as if it were a <td>).
            assert len(cooked_cell_texts) == len(emu_table._header_row.cell_texts)
            as_dict = dict(zip(emu_table._header_row.cell_texts, cooked_cell_texts))

        row = TableRow(tr, cell_nodes, raw_cell_texts, as_dict)

        if is_header:
            emu_table._header_row = row
        else:
            emu_table._data_rows.append(row)

# I'm not sure about applying this,
# versus using the raw spec text.
# But it does seem to simplify things.
def quasi_ecmarkdown(text):
    if re.fullmatch(r'`[^`]*`', text):
        text = text[1:-1]
    text = re.sub(r'\\(.)', r'\1', text)
    text = text.replace('&lt;', '<').replace('&gt;', '>')
    return text

@dataclass
class TableRow:
    tr: HTML.HNode
    cell_nodes: typing.List[HTML.HNode]
    cell_texts: typing.List[str]
    as_dict: typing.Dict

# vim: sw=4 ts=4 expandtab
