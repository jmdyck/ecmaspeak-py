
# ecmaspeak-py/algos.py:
# This module declares the classes and some functions
# relating to the Alg->AlgHeader->AlgDefn hierarchy.
#
# Copyright (C) 2023  J. Michael Dyck <jmdyck@ibiblio.org>

import re, typing
from dataclasses import dataclass

import shared
from HTML import HNode
from shared import spec, stderr
import Pseudocode

# An `Alg` has zero or more `AlgHeader`s,
# each of which has zero or more `AlgDefn`s,
# each of which has a chunk of pseudocode.

# In a lot of cases, those "zero or more" are just "one",
# and the Alg -> AlgHeader -> AlgDefn 'hierarchy'
# seems like pointless indirection.
# Here are the exceptions to that generalization...

# Cases where an Alg has multiple AlgHeaders:
#
# - essential internal methods
#   E.g., the spec has 3 definitions of the internal method [[IsExtensible]],
#   one for each of ordinary object, module namespace exotic object, and Proxy exotic object.
#   So there's an Alg for the name '[[IsExtensible]]',
#   and it has 3 AlgHeaders.
# 
# - "concrete methods" of Records
#   E.g., there's an Alg for `CreateImmutableBinding`,
#   and it has 3 AlgHeaders, one for each of
#   Declarative ER, Object ER, and Global ER.
#
# - the two remaining SDOs that are defined over multiple sections:
#   `Evaluation` and `MV`
#
# - Early Errors
#
# - CharacterValue + IsCharacterClass,
#   where the alg has a header in the main body and one in Annex B

# Cases where an Alg has zero AlgHeaders:
#
# - Shorthands
#   (E.g., ReturnIfAbrupt)
#
# - Operations (mostly numeric) that are defined very briefly
#   (E.g., abs, floor, scf)

# -----

# Cases where an AlgHeader has multiple AlgDefns:
#
# - Most syntax-directed operations.
#   E.g., For 'BoundNames', there's an Alg with a single AlgHeader
#   (because it's defined in only one section), but that AlgHeader
#   has 51 AlgDefns (because there are 51 grammar/algorithm pairs in the section).
#
# - Most Early Errors
#   (because most "Early Errors" sections have multiple grammar/constraint pairs)
#
# - Operations defined in a table (RequireObjectCoercible + ToObject).

# Cases where an AlgHeader has zero AlgDefns:
#
# - CreateImmutableBinding for Object Environment Record
#   and DeleteBinding for Module Environment Record,
#   where the section exists only to say that the method is never called.
#
# - Built-in functions that are just an 'alias' to
#   a function defined elsewhere in the spec.
#   (E.g., Number.parseFloat, Set.prototype.keys, String.prototype.trimLeft)
#
# - Built-in functions that are defined via prose,
#   possibly including a reference to a definition in ECMA-402.
#   (E.g., Number.prototype.toLocaleString, Date.now)
#
# - The first section for 'Evaluation',
#   which exists only to be the landing spot for links.
#
# - Most Host-defined operations
#   (Not all, because a few have a default implementation.)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

spec.alg_info_ = { 'bif': {}, 'op': {} }
# These need to be separate because 'Set' is the name of
# both an abstract operation and a built-in function.

def ensure_alg(alg_species, alg_name):
    bif_or_op = 'bif' if alg_species.startswith('bif:') else 'op'
    iffn = spec.alg_info_[bif_or_op]

    if alg_name in iffn:
        alg_info = iffn[alg_name]
        assert alg_info.name == alg_name
        assert alg_info.species == alg_species
    else:
        alg_info = Alg(alg_name, bif_or_op, alg_species)
        iffn[alg_name] = alg_info

    return alg_info

class Alg:
    # An operation (widely construed) or
    # the algorithmic aspect of a (built-in) function.
    def __init__(self, name, bif_or_op, species):
        self.name = name
        self.bif_or_op = bif_or_op
        self.species = species
        self.invocations = []
        self.callees = set()
        self.callers = set()
        self.headers = []

    def __str__(self):
        return f"{self.bif_or_op}: {self.name}"

    def __lt__(self, other):
        return (
            self.bif_or_op < other.bif_or_op
            or
            self.bif_or_op == other.bif_or_op
            and
            self.name < other.name
        )

    def all_definitions(self):
        return [
            alg_defn
            for alg_header in self.headers
            for alg_defn in alg_header.u_defns
        ]

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

@dataclass
class AlgParam:
    name: str
    punct: str # '' | '[]' | '...'
    nature: str
    decl_node: Pseudocode.ANode = None

# ------------------------------------------------

class AlgHeader:
    def __init__(self):
        self.species = None
        self.name = None
        self.for_phrase = None
        self.for_phrase_node = None
        self.params = None
        self.return_nature_node = None
        self.description_paras = []
        self.u_defns = []
        self.line_num = None

    # --------------------------------------------------------------------------

    def __str__(self):
        return f"""
            AlgHeader:
                name: {self.name}
                species: {self.species}
                for : {self.for_phrase}
                params: {', '.join(
                    param.name + ' : ' + param.nature
                    for param in self.params
                    )
                }
                returns: {self.return_nature_node.source_text() if self.return_nature_node else 'None'}
                # defns: {len(self.u_defns)}
        """

    def __repr__(self):
        return f"AlgHeader(name: {self.name!r})"

    # --------------------------------------------------------------------------

    def param_names(self):
        return [
            param.name
            for param in self.params
        ]

    # --------------------------------------------------------------------------

    def finish_initialization(self):

        self.name_w_markup = self.name
        if self.name.startswith('<'):
            mo = re.fullmatch(r'<dfn [^<>]+>([^<>]+)</dfn>', self.name)
            assert mo
            self.name = mo.group(1)

        # ------------------------------------------------------------

        assert self.params is not None

        assert len([
                param.name
                for param in self.params
                if param.punct == '...'
            ]) in [0,1]

        if self.species.startswith('bif:'):
            for param in self.params:
                if param.nature == 'unknown':
                    if param.punct == '...':
                        param.nature = 'a List of ECMAScript language values'
                    else:
                        param.nature = 'an ECMAScript language value'

        # -------------------------

        assert isinstance(self.description_paras, list)
        desc = ' '.join(self.description_paras)
        desc = re.sub(r'^(!OP|!FUNC|!CM) ', '', desc)
        desc = re.sub(r'^(It|This operation|The job) ', '', desc)
        desc = (desc
            .replace('!OP', 'This operation')
            .replace('!FUNC', 'This function')
        )
        self.description = desc
        # Alternatively: if len(self.description_paras) > 1: make separate <p> elements?

        # -------------------------

        self.parent_alg = ensure_alg(self.species, self.name)
        self.parent_alg.headers.append(self)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def write_header_info():
    stderr("write_header_info ...")

    f = shared.open_for_output('header_info')

    def put(*args): print(*args, file=f)

    for bif_or_op in ['op', 'bif']:
        put('X'*40)
        put(bif_or_op)
        for (alg_name, alg_info) in sorted(spec.alg_info_[bif_or_op].items()):
            n_defns_via_headers = 0
            assert alg_info.name == alg_name
            assert alg_info.bif_or_op == bif_or_op
            put()
            put(f"  {alg_info.name}")
            put(f"    {alg_info.species}")
            put(f"    {len(alg_info.headers)} headers:")
            for alg_header in alg_info.headers:
                assert alg_header.name == alg_name
                assert alg_header.species == alg_info.species
                put(f"      --")
                section = alg_header.section
                put(f"      {section.section_num} {section.section_title}")
                if alg_header.for_phrase: put(f"        for: {alg_header.for_phrase}")
                # alg_header.params
                # alg_header.return_nature_{normal,abrupt}
                # alg_header.description_paras
                put(f"        {len(alg_header.u_defns)} defns")
                n_defns_via_headers += len(alg_header.u_defns)
                for alg_defn in alg_header.u_defns:
                    assert alg_defn.header is alg_header

            assert n_defns_via_headers == len(alg_info.all_definitions())
            # alg_info.invocations
            # alg_info.callees
            # alg_info.callers
        put()

    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

@dataclass
class AlgDefn:
    header: AlgHeader
    discriminator: typing.Union[HNode, str, None]
    kludgey_p: typing.Union[HNode, None]
    anode: Pseudocode.ANode

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab
