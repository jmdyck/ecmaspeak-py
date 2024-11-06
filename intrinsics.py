#!/usr/bin/python3

# ecmaspeak-py/intrinsics.py:
# Code that deals with intrinsic objects.
#
# Copyright (C) 2021  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re
from collections import defaultdict
from dataclasses import dataclass
import typing

import shared
from shared import stderr, spec, msg_at_posn

# ------------------------------------------------------------------------------

def get_pdn(phrase):
    # {phrase} is a string that identifies an intrinsic/global object.
    # Return the PDN (percent-delimited name) for that object.
    #
    # (Generally, this function doesn't know or care whether the object
    # actually exists. It just applies naming conventions.)

    def pc(s): return f"%{s}%"

    if re.fullmatch(r'%[^%]+%', phrase):
        # {phrase} is already a PDN

        if phrase == '%GeneratorFunction.prototype.prototype%':
            # ... but it isn't *the* PDN for that object, this is:
            return '%GeneratorPrototype%'

        if phrase == '%AsyncGeneratorFunction.prototype.prototype%':
            # similar
            return '%AsyncGeneratorPrototype%'

        return phrase

    # --------------
    # fixed phrases:

    if phrase in ['the global object', 'global object']:
        return '%(global)%'
        # It's questionable to treat the global object like an intrinsic

    result = {
        'the constructor of async function objects': '%AsyncFunction%',
        'the constructor of async generator function objects': '%AsyncGeneratorFunction%',
        'the constructor of generator function objects': '%GeneratorFunction%',
        'the super class of all typed Array constructors': '%TypedArray%',
        'the prototype of Iterator Helper objects': '%IteratorHelperPrototype%',
        'the prototype of wrapped iterator objects returned by Iterator.from': '%WrapForValidIteratorPrototype%',
    }.get(phrase)
    if result: return result

    # -----------------------------------------
    # multi-word phrases with 'variable' parts:

    if mo := re.fullmatch(r'the prototype of (.+) [Ii]terator objects', phrase):
        what = mo.group(1)
        return pc(
            ''.join(
                (word[0].upper() + word[1:])
                for word in re.split('[- ]', what)
            ) + 'IteratorPrototype'
        )

    if mo := re.fullmatch(r'(the )?%(\w+)% prototype object', phrase):
        return pc(mo.expand(r'\2.prototype'))

    if mo := re.fullmatch(r'(the )?(\w+) prototype( object)?', phrase):
        path = mo.expand(r'\2.prototype')
        return pc(normalize_property_path(path))
        # normalize_property_path for the "Generator.prototype" check

    if mo := re.fullmatch(r'the (\w+) (constructor|object)', phrase):
        return pc(mo.group(1))

    if mo := re.fullmatch(r'the %(\w+(\.\w+)*)% (object|intrinsic object)', phrase):
        return pc(mo.group(1))

    if mo := re.fullmatch(r'the (\w+) function', phrase):
        return pc(mo.group(1))

    if mo := re.fullmatch(r'(get|set) (.+)', phrase):
        (get_or_set, path) = mo.groups()
        return pc(normalize_property_path(path) + ':' + get_or_set) # or something

    # -----------------------------------------------
    # Anything left should be just a 'property path'.
    # (If it isn't, normalize_property_path will raise an AssertionError.)

    inner = normalize_property_path(phrase)
    return pc(inner)

# ------------------------------------------------------------------------------

def normalize_property_path(path):
    # --------------
    # special cases:

    if path == 'the prototype of generator objects':
        return 'GeneratorPrototype'
    if path == 'the prototype of async generator objects':
        return 'AsyncGeneratorPrototype'

    # --------------------------------
    # base cases (leftmost component):

    if re.fullmatch(r'\w+', path):
        return path

    if mo := re.fullmatch(r'%(\w+)%', path):
        return mo.group(1)

    # ----------------
    # recursive cases:
    # (split off rightmost component of path)

    # property key is a String
    if mo := re.fullmatch(r'(.+)(\.\w+)', path):
        (head, tail) = mo.groups()
        return normalize_property_path(head) + tail

    # property key is a Symbol
    if mo := re.fullmatch(r'(.+) \[ (%Symbol\.\w+%) \]', path):
        (head, tail) = mo.groups()
        return normalize_property_path(head) + f"[{tail}]" # presumably

    # ----------------------------
    # That should cover everything

    assert 0, path

# ------------------------------------------------------------------------------

well_known_intrinsics = {}
global_property_names = set()

# ------------------------------------------------------------------------------

def each_row_in_wki_table(emu_table):
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
            assert global_name not in global_property_names
            global_property_names.add(global_name[1:-1])

        if re.match(r'(A function|An) object that ', assoc):
            phrase = ''
        elif (mo := re.fullmatch(r'The (.+) \(<emu-xref href="[^"]+"></emu-xref>\)', assoc)):
            phrase = 'the ' + mo.group(1)
        else:
            assert 0, assoc

        # --------------------------------------------------

        yield (percent_name, global_name, phrase)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

@dataclass(frozen = True)
class S_InternalSlot:
    name : str
    value: str

    def __str__(self):
        return f"{self.name} with value ({self.value})"


@dataclass # not frozen because may need to change attrs during merging
class S_Property:
    key     : str
    attrs   : dict

    def __init__(self, key, attrs):
        assert isinstance(attrs, dict)
        attr_name_set = set(attrs.keys())
        assert (
            attr_name_set <= set([
                '[[Value]]',
                '[[Writable]]',
                '[[Enumerable]]',
                '[[Configurable]]',
            ])
            or
            attr_name_set <= set([
                '[[Get]]',
                '[[Set]]',
                '[[Enumerable]]',
                '[[Configurable]]',
            ])
        ), attr_name_set

        self.key = key
        self.attrs = attrs

    def kind(self):
        is_data = ('[[Value]]' in self.attrs or '[[Writable]]' in self.attrs)
        is_accessor = ('[[Get]]' in self.attrs or '[[Set]]' in self.attrs)
        assert not (is_data and is_accessor)
        if is_data:
            kind = 'data'
        elif is_accessor:
            kind = 'accessor'
        else:
            kind = 'unknown'
        return kind

    def __str__(self):
        return f"a property with key {self.key} and attributes {self.attrs}"

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def process_intrinsics_facts():
    coalesce_intrinsic_facts()
    apply_defaults()
    determine_creation_order()
    print_intrinsic_info()

def coalesce_intrinsic_facts():
    # Go through all the facts,
    # and accumulate facts about each intrinsic object.

    for section in spec.root_section.each_descendant_that_is_a_section():
        for (L, verb, R) in section.intrinsic_facts_cooked:

            L_intrinsic = ensure_intrinsic_named(L)

            if verb == "exists":
                pass

            elif verb == "is":
                kind = R
                if L_intrinsic.kind is None:
                    L_intrinsic.kind = kind
                elif L_intrinsic.kind == kind:
                    # same
                    pass
                elif (
                    L_intrinsic.kind == 'a constructor' and kind == 'a function object'
                    or
                    L_intrinsic.kind == 'a function object' and kind == 'a constructor'
                ):
                    # They're consistent
                    L_intrinsic.kind = 'a constructor'
                else:
                    # inconsistent? 
                    assert L_intrinsic.kind == kind, \
                        f"? {L_intrinsic.name} kind: {L_intrinsic.kind!r} != {kind!r}"

            elif verb == "has-slot":
                slot = R
                if slot.name not in L_intrinsic.slots:
                    L_intrinsic.slots[slot.name] = slot.value
                else:
                    curr_value = L_intrinsic.slots[slot.name]
                    if curr_value == slot.value:
                        pass
                    elif slot.name == '[[ccb]]':
                        # One says 'emu-alg' and the other says 'prose'
                        L_intrinsic.slots[slot.name] = curr_value.replace('prose in', 'emu-alg in')
                    else:
                        assert curr_value == slot.value, \
                            f"? {L_intrinsic.name} {slot.name}: {curr_value!r} != {slot.value!r}"

            elif verb == 'has-prop':
                L_intrinsic.ensure_property(R)
                # more TODO

            else:
                assert 0, verb

            if 0:
                if phrase.startswith('*') or phrase == 'the empty String':
                    # It expresses a String/Number/Boolean/Null value
                    continue
                elif phrase in ['a function', 'host-defined']:
                    # hm
                    continue
                ensure_intrinsic_named(phrase)

# ------------------------------------------------------------------------------

def apply_defaults():
    for intrinsic in all_intrinsics:
        intrinsic.apply_defaults()

# ------------------------------------------------------------------------------

def determine_creation_order():
    intrinsics_in_rank_ = defaultdict(list)
    for intrinsic in all_intrinsics:
        rank = intrinsic.get_creation_rank()
        intrinsics_in_rank_[rank].append(intrinsic)

    spec.intrinsics_in_creation_order = []
    for (rank, intrinsics_in_rank) in sorted(intrinsics_in_rank_.items()):
        for intrinsic in sorted(intrinsics_in_rank, key=lambda intr: intr.name):
            spec.intrinsics_in_creation_order.append(intrinsic)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def print_intrinsic_info():

    f = shared.open_for_output('intrinsics')
    for intrinsic in sorted(all_intrinsics, key=lambda intr: intr.name):
        intrinsic.dump(f)
    f.close()

    # ----------------------------------------------------------------

    f = shared.open_for_output('intrinsics_anomalies')
    def put(*args): print(*args, file=f)

    for intrinsic in sorted(all_intrinsics, key=lambda intr: intr.name):
        if intrinsic.kind not in [
            'a function object',
            'a constructor',
            'an ordinary object',
            'a String exotic object',
            'an Array exotic object',
            'an immutable prototype exotic object whose other internal methods are ordinary',
        ]:
            put(f"{intrinsic.name} kind = {intrinsic.kind}")

        if intrinsic.kind in ['a function object', 'a constructor']:
            if '[[ccb]]' not in intrinsic.slots:
                put(f"{intrinsic.name} is {intrinsic.kind}, but does not have a [[ccb]] slot")
        else:
            if '[[ccb]]' in intrinsic.slots:
                put(f"{intrinsic.name} is {intrinsic.kind}, but has a [[ccb]] slot")

        for (_, s_prop) in sorted(intrinsic.properties.items()):
            if '[[Value]]' not in s_prop.attrs and '[[Get]]' not in s_prop.attrs:
                put(f"{intrinsic.name} property {s_prop.key}: neither [[Value]] nor [[Get]] is specified")

    # ----------

    sections_for_id_ = defaultdict(list)
    for section in spec.root_section.each_descendant_that_is_a_section():
        for (L, verb, R) in section.intrinsic_facts_raw:
            for ref in [L, R]:
                if (
                    isinstance(ref, str)
                    and re.fullmatch(r'\w+', ref)
                    and not re.fullmatch(r'_\w+_', ref) # ecmarkup alias, for _NativeError_ and _TypedArray_
                ):
                    # {ref} is an identifier,
                    # suggests that there is a global property with that name.
                    sections_for_id_[ref].append(section)

    the_global_object = intrinsic_named_['%(global)%']
    for (identifier, sections) in sections_for_id_.items():
        if f'*"{identifier}"*' in the_global_object.properties:
            # The global object has a property by that name
            pass
        else:
            section_nums = ', '.join( section.section_num for section in sections )
            put(f"no global property named `{identifier}` but section titles suggest otherwise:")
            put(f"    {section_nums}")

    f.close()

    # sys.exit(0)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

all_intrinsics = []
intrinsic_named_ = {}

# ------------------------------------------

def ensure_intrinsic_named(name):
    if name not in intrinsic_named_:
        S_Intrinsic(name)
    return intrinsic_named_[name]

# ------------------------------------------

class S_Intrinsic:
    # An instance of this class records information about an intrinsic object.
    # It isn't an object itself.

    def __init__(self, name):
        # assert re.fullmatch(r'%[^ %]+%', name) # now there can be a %foo% within %bar[...]%
        self.name = name
        self.kind = None
        self.slots = {}
        self.properties = {}

        all_intrinsics.append(self)
        intrinsic_named_[name] = self

    def dump(self, f):
        def put(*args): print(*args, file=f)
        put()
        put('----')
        put(self.name)
        put(f"    creation_rank: {self.creation_rank}")
        put(f"    kind: {self.kind}")
        put(f"    slots:")
        for (slot_name, slot_value) in sorted(self.slots.items()):
            put(f"        {slot_name}: {slot_value}{check_s_value(slot_value)}")
        put(f"    properties:")

        # We're about to list the properties,
        # and we want to do it in a consistent order, to minimize spurious diffs.
        # But a property key is a String or a Symbol, so how do we order them?
        # The way we denote String values here (as in the spec) starts with a '*'.
        # Symbols were formerly denoted starting with '@@' (which comes after '*' in ASCII),
        # so a simple sort on property keys would put all String keys before all Symbol keys.
        #
        # Now (PR #1314), the spec denotes symbol values as %Symbol.foo%,
        # and '%' comes *before* '*' in ASCII, so a simple sort on keys
        # would put all Symbols before all Strings.
        #
        # To preserve the old order (for backwards compatibility),
        # we convert '%' to '@' for the sort key.
        #
        # (Note that this doesn't change anything in self.properties,
        # it only affects the sort keys, which the for-loop discards.)

        def strings_before_symbols(properties_item):
            (prop_key, s_prop) = properties_item
            return prop_key.replace('%', '@')

        for (_, s_prop) in sorted(self.properties.items(), key=strings_before_symbols):
            put(f"        {s_prop.key}")
            if s_prop.attrs is not None:
                put(f"            ({s_prop.kind()} property)")
                for (n,v) in s_prop.attrs.items():
                    if v is not None:
                        put(f"            {n}: {v}{check_s_value(v)}")

    def ensure_property(self, s_prop):
        k = s_prop.key
        if k not in self.properties:
            self.properties[k] = s_prop
        else:
            old_prop = self.properties[k]
            assert old_prop.key == s_prop.key
            old_prop.attrs = merge_propAttrs(old_prop.attrs, s_prop.attrs)

    def apply_defaults(self):

        # ---------------
        # self.kind

        if self.name == '%(global)%':
            assert self.kind is None
            # Might be ordinary or exotic.
            # From clause 19, we know it doesn't have [[Call]] or [[Construct]].
            self.kind = 'host-defined non-function'
        elif self.name == '%Array.prototype[%Symbol.unscopables%]%':
            assert self.kind is None
            # "The initial value ... is an object created by the following steps:"
            # where the object is created by OrdinaryObjectCreate(null)
            self.kind = 'an ordinary object'
        else:
            assert self.kind in [
                'an ordinary object',
                'a function object',
                'a constructor',
                'a String exotic object',
                'an Array exotic object',
                'an immutable prototype exotic object whose other internal methods are ordinary',
            ]

        # ---------------
        # self.slots

        # [[Extensible]]
        # 
        # 18 ECMAScript Standard Built-in Objects:
        #
        #> Unless specified otherwise,
        #> the [[Extensible]] internal slot of a built-in object
        #> initially has the value *true*.

        if '[[Extensible]]' not in self.slots:
            self.slots['[[Extensible]]'] = '*true*'

        # [[Prototype]]
        #
        # 10.3 Built-in Function Objects
        #
        #> Unless otherwise specified
        #> every built-in function object has the %Function.prototype% object
        #> as the initial value of its [[Prototype]] internal slot.
        #
        # 18 ECMAScript Standard Built-in Objects:
        #
        #> Unless otherwise specified
        #> every built-in function and every built-in constructor
        #> has the Function prototype object,
        #> which is the initial value of the expression `Function.prototype` (...),
        #> as the value of its [[Prototype]] internal slot.
        #>
        #> Unless otherwise specified
        #> every built-in prototype object
        #> has the Object prototype object,
        #> which is the initial value of the expression `Object.prototype` (...),
        #> as the value of its [[Prototype]] internal slot,
        #> except the Object prototype object itself.

        if '[[Prototype]]' not in self.slots:
            if self.kind in ['a function object', 'a constructor']:
                Prototype = '%Function.prototype%'
            elif self.name == '%Array.prototype[%Symbol.unscopables%]%':
                # Created via `OrdinaryObjectCreate(*null*)`
                Prototype = '*null*'
            else:
                # Every other intrinsic specifies its [[Prototype]] explicitly.
                assert 0, f"need [[Prototype]] for {self.name}"
            self.slots['[[Prototype]]'] = Prototype

        # ---------------
        # self.properties

        if self.kind in ['a function object', 'a constructor']:

            # --------------------------------------------------------
            # `length`

            # 18 ECMAScript Standard Built-in Objects:
            #
            #> Every built-in function object, including constructors,
            #> has a *"length"* property whose value is a non-negative integral Number.
            #> Unless otherwise specified, this value is equal to
            #> the number of required parameters shown in the subclause heading for the function description.
            #> Optional parameters and rest parameters are not included in the parameter count.
            #>
            #> Unless otherwise specified,
            #> the *"length"* property of a built-in function object has the attributes
            #> { [[Writable]]: *false*, [[Enumerable]]: *false*, [[Configurable]]: *true* }.

            prop_key = '*"length"*'

            ccb = self.slots['[[ccb]]']
            (ccb_style, ccb_section_id) = ccb.split(' in ')
            ccb_section = spec.node_with_id_[ccb_section_id]
            if self.name == '%Function.prototype%':
                assert ccb_section.alg_headers == []
                # There isn't a section dedicated to specifying its behavior.
                # Rather, `Properties of the Function Prototype Object` says:
                #> accepts any arguments and returns *undefined* when invoked.
                # But that section also explicitly defines the value of the *"length"* property,
                # so we it shouldn't be necessary to determine the default value.
                # However, due to the way this code is written,
                # we still have to set this variable to something.
                n_plain_parameters = -1
                # (Negative so that it'll stick out if it ever does get used.)
            else:
                alg_header = ccb_section.alg_headers[0]
                n_plain_parameters = sum(
                    param.punct == ''
                    for param in alg_header.params
                )

            if n_plain_parameters == 0:
                npp = '+0'
            else:
                npp = str(n_plain_parameters)

            default_attrs = {
                '[[Value]]'       : f"*{npp}*<sub>\U0001d53d</sub>",
                '[[Writable]]'    : '*false*',
                '[[Enumerable]]'  : '*false*',
                '[[Configurable]]': '*true*',
            }

            self.apply_defaults_for_property(prop_key, default_attrs)

            # --------------------------------------------------------
            # `name`

            # 18 ECMAScript Standard Built-in Objects:
            #
            #> Every built-in function object, including constructors,
            #> has a *"name"* property whose value is a String.
            #> Unless otherwise specified, this value is
            #> the name that is given to the function in this specification.
            #> Functions that are identified as anonymous functions
            #> use the empty String as the value of the *"name"* property.
            #> For functions that are specified as properties of objects,
            #> the name value is the property name string used to access the function.
            #> Functions that are specified as get or set accessor functions of built-in properties
            #> have *"get"* or *"set"* (respectively) passed to the _prefix_ parameter
            #> when calling CreateBuiltinFunction.
            #>
            #> The value of the *"name"* property is explicitly specified for each built-in functions
            #> whose property key is a Symbol value.
            #> If such an explicitly specified value starts with the prefix *"get "* or *"set "*
            #> and the function for which it is specified is a get or set accessor function of a built-in property,
            #> the value without the prefix is passed to the _name_ parameter,
            #> and the value *"get"* or *"set"* (respectively) is passed to the _prefix_ parameter
            #> when calling CreateBuiltinFunction.</p>
            #>
            #> Unless otherwise specified,
            #> the *"name"* property of a built-in function object has the attributes
            #> { [[Writable]]: *false*, [[Enumerable]]: *false*, [[Configurable]]: *true* }.

            prop_key = '*"name"*'

            if mo := re.search(r'\[%Symbol\.(\w+)%\]:([gs]et)%$', self.name):
                default_name = mo.expand(r'\2 [Symbol.\1]')
            elif mo := re.search(r'\[%Symbol\.(\w+)%\]%$', self.name):
                default_name = mo.expand(r'[Symbol.\1]')
            elif mo := re.search(r'(\w+)%$', self.name):
                default_name = mo.expand(r'\1')
            else:
                assert False, self.name

            default_attrs = {
                '[[Value]]'       : f'*"{default_name}"*',
                '[[Writable]]'    : '*false*',
                '[[Enumerable]]'  : '*false*',
                '[[Configurable]]': '*true*',
            }

            self.apply_defaults_for_property(prop_key, default_attrs)

        # --------------------------------------------------------

        # 18 ECMAScript Standard Built-in Objects:
        #
        #> Every other data property described in clauses
        #> <emu-xref href="#sec-global-object"></emu-xref> through <emu-xref href="#sec-reflection"></emu-xref>
        #> and in Annex <emu-xref href="#sec-additional-built-in-properties"></emu-xref>
        #> has the attributes
        #> { [[Writable]]: *true*, [[Enumerable]]: *false*, [[Configurable]]: *true* }
        #> unless otherwise specified.
        #>
        #> Every accessor property described in clauses
        #> <emu-xref href="#sec-global-object"></emu-xref> through <emu-xref href="#sec-reflection"></emu-xref>
        #> and in Annex <emu-xref href="#sec-additional-built-in-properties"></emu-xref>
        #> has the attributes
        #> { [[Enumerable]]: *false*, [[Configurable]]: *true* }
        #> unless otherwise specified.
        #> If only a get accessor function is described,
        #> the set accessor function is the default value, *undefined*.
        #> If only a set accessor is described
        #> the get accessor is the default value, *undefined*.

        for prop_key in self.properties:
            if prop_key in ['*"length"*', '*"name"*'] and self.kind in ['a function object', 'a constructor']:
                pass # already handled above
            else:
                prop = self.properties[prop_key]
                kind = prop.kind()
                if kind == 'data':
                    default_attrs = {
                        '[[Writable]]'    : '*true*',
                        '[[Enumerable]]'  : '*false*',
                        '[[Configurable]]': '*true*',
                    }
                elif kind == 'accessor':
                    default_attrs = {
                        '[[Enumerable]]'  : '*false*',
                        '[[Configurable]]': '*true*',
                    }
                else:
                    stderr(f"!!! {self.name}'s property {prop_key} has kind {kind!r}")
                    default_attrs = {}
                self.apply_defaults_for_property(prop_key, default_attrs)

    # -------------------------------------------------------------

    def apply_defaults_for_property(self, prop_key, default_attrs):
        if prop_key in self.properties:
            # We have some explicit facts about this property,
            # but maybe not about all the attributes.
            prop = self.properties[prop_key]
            for (attr_name, attr_setting) in default_attrs.items():
                if attr_name in prop.attrs:
                    # We already have an explicit setting for this attribute.
                    if False and prop_key == '*"name"*':
                        explicit_setting = prop.attrs[attr_name]
                        if explicit_setting != attr_setting:
                            print(f"NOTE: {self.name}, property {prop_key}, attribute {attr_name}: explicit setting {explicit_setting} differs from default {attr_setting}")
                else:
                    # There isn't an explicit setting for this attribute.
                    prop.attrs[attr_name] = attr_setting
        else:
            # We don't have any explicit facts about this property.
            self.ensure_property(S_Property(prop_key, default_attrs.copy()))

    # --------------------------------------------------------------------------

    def get_creation_rank(self):
        if hasattr(self, 'creation_rank'):
            return self.creation_rank

        Proto = self.slots['[[Prototype]]']
        if Proto in ['*null*', 'host-defined']:
            rank = 0
        else:
            rank = 1 + intrinsic_named_[Proto].get_creation_rank()
        self.creation_rank = rank
        return rank

    # --------------------------------------------------------------------------

def merge_propAttrs(propAttrs_a, propAttrs_b):
    if propAttrs_a == propAttrs_b: return propAttrs_a

    propAttrs_m = propAttrs_a.copy()
    for (n,v) in propAttrs_b.items():
        if n in propAttrs_m:
            assert v == propAttrs_m[n]
        else:
            propAttrs_m[n] = v
    return propAttrs_m

# def merge_values(va, vb):
#     if va == vb: return va
# 
#     if va is None: return vb
#     if vb is None: return va
# 
#     if va in intrinsic_named_ and vb in intrinsic_named_:
#         ia = intrinsic_named_[va]
#         ib = intrinsic_named_[vb]
#         if ia is ib: return ia.name
# 
#     assert 0, (va, vb)

def check_s_value(v):
    if v in intrinsic_named_:
        return ''
    for pattern in [
        # Undefined:
        r'\*undefined\*',

        # Null:
        r'\*null\*',

        # Boolean:
        r'\*false\*',
        r'\*true\*',

        # Number:
        r'\*NaN\*',
        r'\*\d+\*<sub>\U0001d53d</sub>',
        r'\*\d+\*<sub>\U0001d53d</sub> \(.+\)',
        r'\*-\d+\*<sub>\U0001d53d</sub> \(.+\)',
        r'\*\+0\*<sub>\U0001d53d</sub>',
        r'\*\+∞\*<sub>\U0001d53d</sub>',
        r'\*-∞\*<sub>\U0001d53d</sub>',
        r'the largest positive finite value of the Number type, .+',
        r'the smallest positive value of the Number type, .+',
        r'[Tt]he Number value for .+',
        r'the Element Size value specified in <emu-xref href="#table-the-typedarray-constructors"></emu-xref> for \w+',

        # String:
        r'the empty String',
        r'the String value \*"[^"]*"\*',
        r'\*"[^"]*"\*',

        # Symbol:
        r'the well-known symbol %Symbol\.\w+% \(<emu-xref href="#table-well-known-symbols"></emu-xref>\)',

        # Object:

        # other:
        r'host-defined',
        r'emu-alg in \S+',
        r'prose in \S+',
    ]:
        if re.fullmatch(pattern, v):
            return ''

    return ' [??]'

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_references_to_intrinsics():
    stderr("check_references_to_intrinsics...")

    # We can't just scan through spec.text looking for %...%,
    # because that would find occurrences in element IDs,
    # which are lower-cased.
    # Instead, just look in literal (text) nodes.
    # (Note that this skips occurrences of "%<var>Foo</var>Prototype%".)
    for tnode in spec.doc_node.each_descendant_named('#LITERAL'):
        for mo in re.compile(r'%[^% ]+%').finditer(spec.text, tnode.start_posn, tnode.end_posn):
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
