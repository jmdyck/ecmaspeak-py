# ecmaspeak-py/records.py:
# Code that deals with Records.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re

from shared import spec

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def process_tables():
    for emu_table in spec.doc_node.each_descendant_named('emu-table'):
        caption = emu_table._caption
        header_line = '; '.join(emu_table._header_row.cell_texts)
        
        if 'Field' in caption:
            if re.match(r'^(.+) Fields$', caption):
                pass
            elif re.match(r'^Additional Fields of (.+)$', caption):
                pass
            else:
                assert 0, caption
            assert header_line in [
                'Field Name; Value Type; Meaning',
                'Field Name; Value; Meaning',
                'Field Name; Value; Usage',
                'Field Name; Values of the [[Kind]] field for which it is present; Value; Meaning',
            ], header_line
            for row in emu_table._data_rows:
                if header_line == 'Field Name; Values of the [[Kind]] field for which it is present; Value; Meaning':
                    [field_name, _, value_type, meaning] = row.cell_texts
                else:
                    [field_name, value_type, meaning] = row.cell_texts
                assert re.fullmatch(r'\[\[[A-Z][A-Za-z0-9]+\]\]', field_name), field_name
                # `value_type` is limited, could be checked, but format is ad hoc
                # `meaning` is arbitrary prose

        elif 'Method' in caption and 'Record' in caption:
            assert re.fullmatch(r'(Additional )?(Abstract )?Methods of .+ Records', caption), caption
            assert header_line == 'Method; Purpose'

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
