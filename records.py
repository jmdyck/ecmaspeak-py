# ecmaspeak-py/records.py:
# Code that deals with Records.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import re
from collections import defaultdict

from shared import spec, open_for_output
import Pseudocode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def process_tables():

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

                field_value_type = Pseudocode.parse(row.cell_nodes[-2], 'field_value_type')
                if field_value_type is None: continue
                assert field_value_type.prod.lhs_s == '{FIELD_VALUE_TYPE}'
                value_description = field_value_type.children[0]
                assert value_description.prod.lhs_s == '{VALUE_DESCRIPTION}'

                # `meaning` is arbitrary prose

                record_schema.add_field_decl(FieldDecl(field_name, value_type, meaning, value_description))

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

    # 6.2.6 "The Property Descriptor Specification Type":
    #> Values of the Property Descriptor type are Records.
    #> Each field's name is an attribute name
    #> and its value is a corresponding attribute value
    #> as specified in <emu-xref href="#sec-property-attributes"></emu-xref>.
    # Presumably there's no "Fields" table because
    # such a table would basically just duplicate
    # the "Property Attributes" tables.
    #
    record_schema = ensure_RecordSchema('Property Descriptor')
    record_schema.add_field_decl(FieldDecl('[[Get]]',          'an Object or *undefined*', ''))
    record_schema.add_field_decl(FieldDecl('[[Set]]',          'an Object or *undefined*', ''))
    record_schema.add_field_decl(FieldDecl('[[Value]]',        'an ECMAScript language value', ''))
    record_schema.add_field_decl(FieldDecl('[[Writable]]',     'a Boolean', ''))
    record_schema.add_field_decl(FieldDecl('[[Enumerable]]',   'a Boolean', ''))
    record_schema.add_field_decl(FieldDecl('[[Configurable]]', 'a Boolean', ''))

    # 9.1 "Environment Records":
    #> Every Environment Record has an [[OuterEnv]] field,
    #> which is either *null* or a reference to an outer Environment Record.
    #
    record_schema = ensure_RecordSchema('Environment Record')
    assert len(record_schema.addl_field_decls) == 0
    record_schema.add_field_decl(FieldDecl('[[OuterEnv]]', '*null* or an Environment Record', 'used to model the logical nesting of Environment Record values'))

    # 16.2.1.4 "Abstract Module Records":
    # (on the `ResolveExport` row of the "Abstract Methods of Module Records" table)
    #> Bindings are represented by a <dfn>ResolvedBinding Record</dfn>,
    #> of the form { [[Module]]: Module Record, [[BindingName]]: String | ~namespace~ }.
    #
    record_schema = ensure_RecordSchema('ResolvedBinding Record')
    record_schema.add_field_decl(FieldDecl('[[Module]]', 'a Module Record', ''))
    record_schema.add_field_decl(FieldDecl('[[BindingName]]', 'a String or ~namespace~', ''))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def ensure_RecordSchema(tc_schema_name):
    if tc_schema_name in spec.RecordSchema_for_name_:
        return spec.RecordSchema_for_name_[tc_schema_name]
    elif tc_schema_name == TC_SCHEMA_NAME_FOR_ROOT_SCHEMA:
        # Not in spec.RecordSchema_for_name_
        return root_schema
    else:
        super_tc_schema_name = sub_to_super_relation.get(tc_schema_name, TC_SCHEMA_NAME_FOR_ROOT_SCHEMA)
        # This means that a Record schema that is not declared to be
        # a sub-schema of some other Record schema
        # is here represented as a sub-schema of the 'root' schema.
        # I.e., all record schemas are in a single hierarchy,
        # which makes some processing easier.

        return RecordSchema(tc_schema_name, super_tc_schema_name)
        # which has a side-effect of adding the schema to spec.RecordSchema_for_name_

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
    def __init__(self, tc_schema_name, super_tc_schema_name):
        self.tc_schema_name = tc_schema_name
        self.addl_field_decls = {}
        self.addl_method_decls = {}
        self.method_defns = {}
        self.sub_schemas = []

        if super_tc_schema_name is None:
            assert tc_schema_name == TC_SCHEMA_NAME_FOR_ROOT_SCHEMA # just checking
            self.super_schema = None
            self.level = 0
            spec.root_RecordSchema = self
            # Don't put the root schema into spec.RecordSchema_for_name_
        else:
            self.super_schema = ensure_RecordSchema(super_tc_schema_name)
            self.super_schema.sub_schemas.append(self)
            self.level = 1 + self.super_schema.level
            spec.RecordSchema_for_name_[tc_schema_name] = self

    def __repr__(self):
        return f"RecordSchema({self.tc_schema_name!r}, {None if self.super_schema is None else self.super_schema.tc_schema_name!r})"

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
            if sup.tc_schema_name == TC_SCHEMA_NAME_FOR_ROOT_SCHEMA: return
            yield sup

    def preorder_traverse_subtree(self):
        yield self
        for sub in self.sub_schemas:
            yield from sub.preorder_traverse_subtree()

spec.RecordSchema_for_name_ = {}
TC_SCHEMA_NAME_FOR_ROOT_SCHEMA = 'Empty Record'
root_schema = RecordSchema(TC_SCHEMA_NAME_FOR_ROOT_SCHEMA, None)

class FieldDecl:
    def __init__(self, name, nature, meaning, value_description=None):
        assert re.fullmatch(r'\[\[[A-Z][A-Za-z0-9]+\]\]', name), name
        # `nature` is limited, could be checked, but format is ad hoc (but see PR #2602).
        # `meaning` is arbitrary prose
        self.name = name
        self.nature = nature
        self.meaning = meaning
        self.value_description = value_description

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
    f = open_for_output('record_schemas')
    def output(*args): print(*args, file=f)

    def dump_schema(rs):
        ind = '        ' * (rs.level-1)

        output()
        output(f"{ind}{rs.tc_schema_name}:")

        if rs.super_schema is None or rs.super_schema is root_schema:
            addl = ''
        else:
            addl = 'additional '

        output(f"{ind}    {addl}fields:")
        if rs.addl_field_decls:
            for field_decl in rs.addl_field_decls.values():
                output(f"{ind}      -")
                output(f"{ind}        name:    {field_decl.name}")
                output(f"{ind}        nature:  {field_decl.nature}")
                output(f"{ind}        meaning: {field_decl.meaning}")
                # output(f"{ind}    val desc: {field_decl.value_description}")
        else:
            output(f"{ind}        (none)")

        if rs.addl_method_decls:
            output()
            output(f"{ind}    {addl}methods:")
            for method_decl in rs.addl_method_decls.values():
                single_line_purpose = re.sub(r'\s+', ' ', method_decl.purpose)
                output(f"{ind}      -")
                output(f"{ind}        signature: {method_decl.signature}")
                output(f"{ind}        purpose:   {single_line_purpose}")

        if rs.method_defns:
            output()
            output(f"{ind}    method definitions:")
            for method_defn in rs.method_defns.values():
                # output(f"{ind}        {method_defn.name}")
                # output(f"{ind}        {method_defn.alg_header}")
                # output(f"{ind}        {method_defn.alg_defn}")

                section = method_defn.alg_header.section
                output(f"{ind}        {section.section_num} {section.section_title}")

                if method_defn.alg_defn is None:
                    # This method definition "is never used within this specification".
                    # defn_part += '*'
                    pass
                else:
                    # defn_part += str(method_defn.alg_defn)
                    pass
                # output(f"{ind}        {defn_part}")

        if rs.sub_schemas:
            output()
            output(f"{ind}    sub-schemas:")
            for sub_schema in rs.sub_schemas:
                dump_schema(sub_schema)

    for schema in root_schema.sub_schemas:
        dump_schema(schema)

    output()
    output("=" * 111)

    # --------------------------------------------------------------------------

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

    for rs in root_schema.sub_schemas:
        if rs.sub_schemas:
            print_hierarchy(rs)

    f.close()

# vim: sw=4 ts=4 expandtab
