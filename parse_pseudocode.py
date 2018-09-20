#!/usr/bin/python3

# ecmaspeak-py/parse_pseudocode.py:
# Parse various flavors of ECMASpeak pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, time, math
from collections import defaultdict

from Pseudocode_Parser import Pseudocode_Parser, reo_cache
import shared
from shared import spec, stderr

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def main():
    shared.register_output_dir(sys.argv[1])
    spec.restore()
    parse_emu_eqns()
    parse_early_errors()
    parse_inline_sdo()
    parse_emu_algs()
    spec.save()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_emu_eqns():
    stderr()
    stderr("parse_emu_eqns...")

    emu_eqn_parser = Emu_Eqn_Parser()

    for emu_eqn in spec.doc_node.each_descendant_named('emu-eqn'):
        st = emu_eqn.inner_source_text()
        if '=' not in st:
            # The content is at best a formula or expression;
            # it doesn't define anything.
            # I suppose I could parse it for conformance to {EXPR},
            # but to what end?
            # Skip it.
            continue

        if 'aoid' not in emu_eqn.attrs:
            # There are a few of these:
            #     abs(_k_) &lt; abs(_y_) and _x_-_k_ = _q_ &times; _y_
            #     floor(_x_) = _x_-(_x_ modulo 1)
            #     MonthFromTime(0) = 0
            #     WeekDay(0) = 4
            #     _t_<sub>local</sub> = _t_
            #     _a_ =<sub>CF</sub> _b_
            #     _comparefn_(_a_, _b_) = 0
            # They aren't definitions.
            # Skip it.
            continue

        aoid = emu_eqn.attrs['aoid']
        # id = emu_eqn.attrs['id']
        # assert (id == 'eqn-' + aoid) or (id == 'eqn-DaysFromYear' and aoid == 'DayFromYear')
        # 'id' not defined for 'DateFromTime'

        tree = emu_eqn_parser.parse_and_handle_errors(emu_eqn.inner_start_posn, emu_eqn.inner_end_posn)
        emu_eqn._syntax_tree = tree

    emu_eqn_parser.report()

class Emu_Eqn_Parser(Pseudocode_Parser):
    def __init__(self):
        Pseudocode_Parser.__init__(self, 'emu_eqn')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_early_errors():
    stderr()
    stderr("parse_early_errors...")

    ee_parser = Early_Error_Parser()

    # XXX prose 'superstructure' outside early error rules:
    #
    # sec-object-initializer-static-semantics-early-errors:
    # extra paragraph that constrains application of subsequent emu-grammar + ul
    #
    # sec-for-in-and-for-of-statements-static-semantics-early-errors:
    # extra paragraph that is logically scoped to two bullets of three,
    # but 
    #
    # sec-performeval-rules-outside-functions
    # sec-performeval-rules-outside-methods
    # sec-performeval-rules-outside-constructors
    # Paragraph says (vaguely) when the rule is applied.
    # Algo for PerformEval say exactly when they're applied.
    # See PR #1245.

    something = defaultdict(list)

    for s in spec.doc_node.each_descendant_that_is_a_section():
        if s.section_kind == 'early_errors':
            assert not s.contains_inline_items

            if 0:
                x = re.sub(r'\bemu-grammar ul\b', 'X X',
                        ' '.join(child.element_name for child in s.block_children)
                    )
                x = x.split()
                assert len(x) == len(s.block_children)
                for (block, x) in zip(s.block_children, x):
                    if x == 'X': continue
                    if block.element_name == 'emu-note': continue
                    print('--------------------------')
                    print(s.section_id)
                    print()
                    print(block.source_text())

            for block in s.block_children:
                if block.element_name == 'emu-grammar':
                    curr_emu_grammar = block
                elif block.element_name == 'ul':
                    for li in block.children:
                        if li.element_name == 'li':
                            tree = ee_parser.parse_and_handle_errors(li.start_posn, li.end_posn)
                            li._syntax_tree = tree
                    # XXX connect production with block


    ee_parser.report()

class Early_Error_Parser(Pseudocode_Parser):
    def __init__(self):
        Pseudocode_Parser.__init__(self, 'early_error')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_inline_sdo():
    stderr()
    stderr("parse_inline_sdo...")

    inline_sdo_parser = Inline_SDO_Parser()

    for s in spec.doc_node.each_descendant_that_is_a_section():
        if s.section_kind == 'syntax_directed_operation':
            for ul in s.block_children:
                if ul.element_name == 'ul':
                    if re.match(r'^<li>\n +it is not `0`; or\n +</li>$', ul.children[1].source_text()):
                        # "A digit is significant if ..." in "Runtime Semantics: MV" and "Static Semantics: MV"
                        continue
                    for child in ul.children:
                        if child.element_name == '#LITERAL':
                            assert child.is_whitespace()
                            continue

                        assert child.element_name == 'li'
                        tree = inline_sdo_parser.parse_and_handle_errors(child.start_posn, child.end_posn)
                        child._syntax_tree = tree

    inline_sdo_parser.report()

class Inline_SDO_Parser(Pseudocode_Parser):
    def __init__(self):
        Pseudocode_Parser.__init__(self, 'inline_SDO')

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def parse_emu_algs():
    stderr()
    stderr("parse_emu_algs...")

    emu_alg_parser = Emu_Alg_Parser()

    t_start = time.time()

    parse_count = 0

    def try_to_parse(start_posn, end_posn):
        nonlocal parse_count
        parse_count += 1
        if parse_count % 20 == 0:
            print('.', file=sys.stderr, end='')
            sys.stderr.flush()
        tree = emu_alg_parser.parse_and_handle_errors(start_posn, end_posn)
        return tree

    for emu_alg in spec.doc_node.each_descendant_named('emu-alg'):
        cc_section = emu_alg.closest_containing_section()
        if cc_section.section_title == 'Algorithm Conventions':
            # stderr("skipping Algorithm Conventions")
            continue
            # because some of the <emu-alg>s in that section aren't really parseable

        x = '\n            5. Otherwise, let '
        if spec.text[emu_alg.inner_start_posn:emu_alg.inner_start_posn+len(x)] == x:
            # stderr("skipping 5. Otherwise!")
            continue
            # because I can't parse an "Otherwise" without a preceding "If"
            # (NumberToString)

        if 1:
            tree = try_to_parse(emu_alg.inner_start_posn, emu_alg.inner_end_posn)
            emu_alg._syntax_tree = tree
        else:
            # used this when I was parsing individual lines:
            for mo in re.compile(r'(?m)^ +\d+\. .+\n').finditer(
                spec.text,
                emu_alg.inner_start_posn,
                emu_alg.inner_end_posn
            ):
                (line_start, line_end) = mo.span(0)
                try_to_parse(line_start, line_end)

    print(file=sys.stderr)

    t_end = time.time()
    stderr("parsing %d emu-algs took %d seconds" % (parse_count, t_end-t_start))

    emu_alg_parser.report()

# ------------------------------------------------------------------------------

class Emu_Alg_Parser(Pseudocode_Parser):
    def __init__(self):
        Pseudocode_Parser.__init__(self, 'emu_alg')

        # To handle the {_INDENT} and {_OUTDENT} symbols, ...
        indent_info = [
            (mo.start(), mo.end() - mo.start())
            for mo in re.finditer(r'(?m)^ *', shared.spec_text)
        ]
        indent_change_info = dict(
            (this_posn, this_ind - prev_ind)
            for ((_, prev_ind),(this_posn, this_ind)) in zip([(None,0)] + indent_info[:-1], indent_info)
        )
        self.dent_symbols = {}
        for (posn, indentation_change) in indent_change_info.items():
            if indentation_change % 2 != 0:
                shared.stderr("Warning: odd indentation-change (%d)" % indentation_change)
            n_dents = abs(indentation_change) / 2

            if indentation_change > 0:
                symbol = '{_INDENT}'
            elif indentation_change < 0:
                symbol = '{_OUTDENT}'
            else:
                symbol = None

            self.dent_symbols[posn] = (symbol, n_dents)

    # override:
    def _matcher(self, curr_posn, end_posn, terminals):
        # print(curr_posn, len(terminals))
        # if curr_posn == 2022487: pdb.set_trace()
        # if '[ ]+<figure>' in terminals: pdb.set_trace()
        # if r'(?=\n)' in terminals: pdb.set_trace()

        FRAC_PER_DENT = 1/32
        MAX_N_DENTS_CHANGE = 31

        results = []

        if isinstance(curr_posn, float):
            # We can only accept '{_INDENT}' or '{_OUTDENT}' or '{_NL}' at this position.

            int_posn = math.floor(curr_posn)
            frac_posn = curr_posn - int_posn
            assert frac_posn != 0

            assert shared.spec_text[int_posn] == '\n'
            (dent_symbol, n_dents) = self.dent_symbols[int_posn+1]
            assert dent_symbol in ['{_INDENT}', '{_OUTDENT}']

            if dent_symbol in terminals or '{_NL}' in terminals:

                p = round(frac_posn / FRAC_PER_DENT)
                # p == 0 was where we recognized the first dent,
                # p == 1 is where we recognize the second dent,
                # etc, up to
                # p == n_dents-1 is where we recognize the last dent,
                # p == n_dents is where we recognize the NL

                if p < n_dents and dent_symbol in terminals:
                    results.append( (dent_symbol, curr_posn + FRAC_PER_DENT, None) )
                elif p == n_dents and '{_NL}' in terminals:
                    results.append( ('{_NL}', int_posn+1, None) )
                else:
                    # assert 0
                    pass

        else:
            assert isinstance(curr_posn, int)

            for T in terminals:

                if T in ['{_INDENT}', '{_OUTDENT}', '{_NL}']:
                    if shared.spec_text[curr_posn] == '\n':
                        (dent_symbol, n_dents) = self.dent_symbols[curr_posn+1]
                        if n_dents == 0 and T == '{_NL}':
                            results.append( (T, curr_posn+1, None) )
                        elif n_dents > 0 and T == dent_symbol:
                            results.append( (T, curr_posn + FRAC_PER_DENT, None) )

                else:
                    reo = reo_cache[T]
                    mo = reo.match(shared.spec_text, curr_posn, end_posn)
                    if mo:
                        if reo.groups == 0:
                            st = None
                        elif reo.groups == 1:
                            st = mo.group(1)
                        else:
                            assert 0
                        results.append( (T, mo.end(0), st) )

        if False and len(results) > 1:
            s = ' '.join(repr(T) for (T, end, st) in results)
            shared.stderr(f"returning {len(results)} results: {s}")

        return results

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

main()

# vim: sw=4 ts=4 expandtab
