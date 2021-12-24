# ecmaspeak-py/records.py:
# Code that deals with Records.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re
from collections import defaultdict

from shared import spec, msg_at_node, open_for_output
from nature import check_nature

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def process_tables():

    spec.RecordSchema_for_name_ = {}

    for emu_table in spec.doc_node.each_descendant_named('emu-table'):
        caption = emu_table._caption
        header_line = '; '.join(emu_table._header_row.cell_texts)

        # tc_schema_name:
        # "tc" is for "title-cased" (because we're extracting it from a table caption),
        # which might not be the casing as used elsewhere.

        if 'Field' in caption:
            if mo := re.fullmatch(r'(.+) Fields', caption):
                tc_schema_name = mo.group(1)
            elif mo := re.fullmatch(r'Additional Fields of (.+)s', caption):
                tc_schema_name = mo.group(1)
            else:
                assert 0, caption
            assert (
                tc_schema_name.endswith(' Record')
                or
                tc_schema_name.endswith(' Event')
                or
                tc_schema_name == 'PrivateElement'
            )
            record_schema = ensure_RecordSchema(tc_schema_name)

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

                for warning in check_nature(value_type):
                    msg_at_node(row.cell_nodes[-2], warning)

                # `meaning` is arbitrary prose

                record_schema.add_field_decl(FieldDecl(field_name, value_type, meaning))

        elif 'Method' in caption and 'Record' in caption:
            if mo := re.fullmatch(r'(Additional )?(Abstract )?Methods of (.+ Record)s', caption):
                tc_schema_name = mo.group(3)
            else:
                assert 0, caption
            record_schema = ensure_RecordSchema(tc_schema_name)

            assert header_line == 'Method; Purpose'
            for row in emu_table._data_rows:
                [method_signature, method_purpose] = row.cell_texts
                record_schema.add_method_decl(MethodDecl(method_signature, method_purpose))

    # So that covers all Record-schemas that are declared
    # via "Fields" table and/or "Methods" table.
    # However, there are a couple more...

    # The PropertyDescriptor schema is defined in
    # "The Property Descriptor Specification Type":
    #> Values of the Property Descriptor type are Records.
    #> Each field's name is an attribute name
    #> and its value is a corresponding attribute value
    #> as specified in <emu-xref href="#sec-property-attributes"></emu-xref>.
    # Presumably there's no "Fields" table because
    # such a table would basically just duplicate
    # the "Property Attributes" tables.
    record_schema = ensure_RecordSchema('PropertyDescriptor')
    record_schema.add_field_decl(FieldDecl('[[Get]]',          'Object | Undefined', ''))
    record_schema.add_field_decl(FieldDecl('[[Set]]',          'Object | Undefined', ''))
    record_schema.add_field_decl(FieldDecl('[[Value]]',        'Any ECMAScript language type', ''))
    record_schema.add_field_decl(FieldDecl('[[Writable]]',     'Boolean', ''))
    record_schema.add_field_decl(FieldDecl('[[Enumerable]]',   'Boolean', ''))
    record_schema.add_field_decl(FieldDecl('[[Configurable]]', 'Boolean', ''))

    # The ResolvedBinding Record schema is declared within one cell
    # of the "Abstract Methods of Module Records" table.
    #> Bindings are represented by a <dfn>ResolvedBinding Record</dfn>,
    #> of the form { [[Module]]: Module Record, [[BindingName]]: String | ~namespace~ }.
    record_schema = ensure_RecordSchema('ResolvedBinding Record')
    record_schema.add_field_decl(FieldDecl('[[Module]]', 'Module Record', ''))
    record_schema.add_field_decl(FieldDecl('[[BindingName]]', 'String | ~namespace~', ''))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def ensure_RecordSchema(tc_schema_name):
    if tc_schema_name in spec.RecordSchema_for_name_:
        return spec.RecordSchema_for_name_[tc_schema_name]
    else:
        record_schema = RecordSchema(tc_schema_name)
        spec.RecordSchema_for_name_[tc_schema_name] = record_schema
        return record_schema

# There are a couple of Record-schema hierarchies,
# and we want to capture that hierarchy in RecordSchema instances.
# Unfortunately, the spec isn't consistent about how it conveys that info,
# so I'll just hard-code it.

sub_to_super_relation = {
    #> Environment Records can be thought of as
    #> existing in a simple object-oriented hierarchy
    #> where Environment Record is an abstract class
    #> with three concrete subclasses:
    #> declarative Environment Record,
    #> object Environment Record,
    #> and global Environment Record.
    #> Function Environment Records and module Environment Records
    #> are subclasses of declarative Environment Record.
    #
    # (I'm going to avoid using 'class',
    # because there's already ambiguity with
    # ECMAScript classes and Python classes.
    # Instead, I'll use the terms sub-schema and super-schema.)

    'Declarative Environment Record': 'Environment Record',
    'Object Environment Record'     : 'Environment Record',
    'Global Environment Record'     : 'Environment Record',
    'Function Environment Record'   : 'Declarative Environment Record',
    'Module Environment Record'     : 'Declarative Environment Record',

    'Cyclic Module Record'     : 'Module Record',
    'Source Text Module Record': 'Cyclic Module Record',
}

class RecordSchema:
    def __init__(self, tc_schema_name):
        self.tc_schema_name = tc_schema_name
        self.addl_field_decls = {}
        self.addl_method_decls = {}
        self.method_defns = {}
        self.sub_schemas = []

        if tc_schema_name == '':
            self.super_schema = None
            self.level = 0
        elif tc_schema_name in sub_to_super_relation:
            super_tc_schema_name = sub_to_super_relation[tc_schema_name]
            self.super_schema = ensure_RecordSchema(super_tc_schema_name)
            self.super_schema.sub_schemas.append(self)
            self.level = 1 + self.super_schema.level
        else:
            self.super_schema = EMPTY_record_schema
            # That is, a Record schema that is not declared to be
            # a sub-schema of some other Record schema
            # is here represented as a sub-schema of the Empty Record schema.
            # I think this will be useful, but maybe not.
            self.super_schema.sub_schemas.append(self)
            self.level = 1

    def __str__(self):
        return f"RecordSchema({self.tc_schema_name!r}, {len(self.addl_field_decls)} fields, {len(self.addl_method_decls)} methods, {len(self.sub_schemas)} sub-schemas)"

    def add_field_decl(self, field_decl):
        assert not self.somebody_declares_field(field_decl.name)
        self.addl_field_decls[field_decl.name] = field_decl

    def add_method_decl(self, method_decl):
        assert not self.somebody_declares_method(method_decl.name)
        self.addl_method_decls[method_decl.name] = method_decl

    def add_method_defn(self, method_defn):
        assert self.somebody_declares_method(method_defn.name)
        assert method_defn.name not in self.method_defns
        self.method_defns[method_defn.name] = method_defn

    def somebody_declares_field(self, field_name):
        # This schema, or a schema on its super-schema chain,
        # declares a field with the given name.
        return any(
            field_name in rs.addl_field_decls
            for rs in self.self_and_supers()
        )

    def somebody_declares_method(self, method_name):
        return any(
            method_name in rs.addl_method_decls
            for rs in self.self_and_supers()
        )

    def self_and_supers(self):
        yield self
        sup = self
        while True:
            sup = sup.super_schema
            if sup is EMPTY_record_schema: return
            yield sup

    def preorder_traverse_subtree(self):
        yield self
        for sub in self.sub_schemas:
            yield from sub.preorder_traverse_subtree()

EMPTY_record_schema = RecordSchema('')

class FieldDecl:
    def __init__(self, name, nature, meaning):
        assert re.fullmatch(r'\[\[[A-Z][A-Za-z0-9]+\]\]', name), name
        # `nature` is limited, could be checked, but format is ad hoc (but see PR #2602).
        # `meaning` is arbitrary prose
        self.name = name
        self.nature = nature
        self.meaning = meaning

class MethodDecl:
    def __init__(self, signature, purpose):
        assert isinstance(signature, str)
        assert isinstance(purpose, str)
        self.signature = signature
        self.purpose = purpose

        mo = re.fullmatch(r'([A-Z]\w+)( *)\((.*)\)', signature)
        assert mo, signature
        (self.name, gap, parameter_list_str) = mo.groups()
        # TODO: complain if gap != ''
        # TODO: complain if parameter_list_str needs trimming
        parameter_list_str = parameter_list_str.strip()

class MethodDefn:
    def __init__(self, alg_header, alg_defn):
        self.alg_header = alg_header
        self.alg_defn = alg_defn
        self.name = self.alg_header.name

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def print_schema_hierarchies():
    f = open_for_output('record_schema_hierarchies')
    def output(*args): print(*args, file=f)

    def print_hierarchy(root):
        root_abbrev = ''.join(
            word[0]
            for word in root.tc_schema_name.split()
        )

        depth = get_depth_of_subtree(root)

        col_keys = []
        col_keys.append('method_name')
        for rs in root.preorder_traverse_subtree():
            col_keys.append(rs.tc_schema_name)

        row_keys = []
        for level in range(1, depth+1):
            row_keys.append(f"HEADER LEVEL {level}")
        row_keys.append("LINE AFTER HEADERS")
        for rs in root.preorder_traverse_subtree():
            for method_name in rs.addl_method_decls:
                row_key = f"{rs.tc_schema_name}/{method_name}"
                row_keys.append(row_key)
            if rs.addl_method_decls:
                row_key = f"LINE AFTER {rs.tc_schema_name}"
                row_keys.append(row_key)

        content_for_rowcol_ = defaultdict(str)
        def set_cell(row_key, col_key, content):
            assert row_key in row_keys
            assert col_key in col_keys
            rc_key = (row_key, col_key)
            assert rc_key not in content_for_rowcol_
            content_for_rowcol_[rc_key] = content

        for rs in root.preorder_traverse_subtree():
            col_key = rs.tc_schema_name

            # column label
            row_key = f"HEADER LEVEL {rs.level}"
            header_text = rs.tc_schema_name.replace(root.tc_schema_name, root_abbrev)
            set_cell(row_key, col_key, header_text)

            # row label
            for method_name in rs.addl_method_decls:
                row_key = f"{rs.tc_schema_name}/{method_name}"
                set_cell(row_key, "method_name", method_name)

            # "body" cells
            for sup in rs.self_and_supers():
                for method_name in sup.addl_method_decls:
                    row_key = f"{sup.tc_schema_name}/{method_name}"

                    # Does {rs} have a declaration (table entry) for this method?
                    if method_name in rs.addl_method_decls:
                        decl_part = '#'
                    else:
                        decl_part = ' '

                    # Does {rs} have a definition (algorithm) for this method?
                    if method_name in rs.method_defns:
                        method_defn = rs.method_defns[method_name]
                        defn_part = method_defn.alg_header.section.section_num
                        if method_defn.alg_defn is None:
                            # This method definition "is never used within this specification".
                            defn_part += '*'
                    else:
                        defn_part = ''

                    cell_content = f"{decl_part} {defn_part}"
                    set_cell(row_key, col_key, cell_content)

        # Calculate the width of each column
        width_of_col_ = defaultdict(int)
        for ((row_key, col_key), content) in content_for_rowcol_.items():
            width_of_col_[col_key] = max(width_of_col_[col_key], len(content))

        # Print each row
        output()
        output(f"{root.tc_schema_name} ('{root_abbrev}')")
        for row_key in row_keys:
            row_string = ''
            for col_key in col_keys:
                rc_key = (row_key, col_key)
                if row_key.startswith("LINE"):
                    assert rc_key not in content_for_rowcol_
                    row_string += '-' * (2 + width_of_col_[col_key]) + '+'
                else:
                    cell_string = content_for_rowcol_[rc_key].ljust(width_of_col_[col_key])
                    row_string += f" {cell_string} |"
            output(row_string)


    def get_depth_of_subtree(rs):
        if rs.sub_schemas:
            return 1 + max(
                get_depth_of_subtree(sub)
                for sub in rs.sub_schemas
            )
        else:
            return 1

    for rs in EMPTY_record_schema.sub_schemas:
        if rs.sub_schemas:
            print_hierarchy(rs)

    f.close()

# vim: sw=4 ts=4 expandtab