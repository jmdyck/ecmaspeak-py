#!/usr/bin/python3

# ecmaspeak-py/Pseudocode_Parser.py:
# Parse various flavors of ECMASpeak pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, collections, pdb, math, functools, os, re

from LR_Parser import LR_Parser, ParsingError
# import Earley
import shared

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Pseudocode_Parser:
    def __init__(self, file_base):
        self.file_base = file_base

        grammar_string = open(f"{os.path.dirname(__file__)}/{file_base}.grammar", 'r', encoding='utf-8').read()

        self.productions = convert_grammar_string_to_productions(grammar_string)
        simple_prods = [
            (prod.lhs_s, prod.rhs_pieces)
            for prod in self.productions
        ]
        # LR
        self.lr_parser = LR_Parser('SLR(1)', simple_prods, 'silent')

        #   # Earley (attempt, doesn't work)
        #   self.eparser = Earley.Parser(simple_prods, '*EOI*')

        if shared.g_outdir:
            self.f_errors = shared.open_for_output(file_base + '_errors')
            self.f_ambig = shared.open_for_output(file_base + '_ambig')
            self.f_parsed = shared.open_for_output(file_base + '_parsed')
        else:
            # testing
            self.f_ambig = sys.stdout

        self.error_count = 0
        self.group_errors_by_expectation = True

        if self.group_errors_by_expectation:
            self.error_posns = collections.defaultdict(list)

    def _reducer(self, pi, reductands, s_posn, e_posn):
        prod = self.productions[pi]
        prod.n_reductions += 1
        assert len(reductands) == len(prod.rhs_pieces)

        if prod.lhs_s.startswith('{_'):
            # We're not interested in the details.
            return None

        node_children = []
        for red in reductands:
            if red is None:
                # rhs_piece is a regex with no capturing group
                # or is an uninteresting nonterminal
                continue
            node_children.append(red)

        node = ANode(prod, node_children, s_posn, e_posn)
        return node

    def _matcher(self, curr_posn, end_posn, terminals):
        results = []
        for T in terminals:

            if T == '{_NL}':
                if shared.spec_text[curr_posn] == '\n':
                    results.append( (T, curr_posn+1, None) )
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

        return results

    def parse_and_handle_errors(self, start_posn, end_posn):
        try:
            # LR
            def matcher_for_gparse(curr_posn, terminals):
                return self._matcher(curr_posn, end_posn, terminals)

            results = self.lr_parser.gparse(matcher_for_gparse, self._reducer, start_posn)
            #   # Earley
            #   curr_posn = start_posn
            #   def get_next_token(expected_terminals):
            #       nonlocal curr_posn
            #       results = []
            #       for T in expected_terminals:
            #           mo = reo_cache[T].match(shared.spec_text, curr_posn, end_posn)
            #           if mo:
            #               results.append( (mo.end(0), T) )
            #       assert len(results) > 0
            #       if len(results) > 1:
            #           results.sort(reverse=True)
            #           assert results[0][0] > results[1][0] # XXX
            #       (tok_end, T) = results[0]
            #       token = ANode(T, [
            #           shared.spec_text[curr_posn:tok_end]
            #       ])
            #       curr_posn = tok_end
            #       return token
            #
            #   results = self.eparser.parse('{START}', get_next_token)

        except ParsingError as e:
            self.error_count += 1
            if self.group_errors_by_expectation:
                self.error_posns[tuple(e.expecting)].append(e.posn)
            else:
                print(
                    '\n'
                    +
                    shared.source_line_with_caret_marking_column(e.posn)
                    +
                    '\n'
                    +
                    "Expecting: "
                    +
                    ' '.join(e.expecting),
                    file=self.f_errors
                )
            print('(Error)', file=self.f_parsed)
            return None

        if len(results) != 1:
            print('-------------------------------', file=self.f_ambig)
            for result in results:
                result.printTree(self.f_ambig)

        result = results[0]

        def count(node):
            if isinstance(node, str): return
            assert isinstance(node, ANode)
            node.prod.n_delivered_instances += 1
            for child in node.children:
                count(child)

        count(result)

        result.printTree(self.f_parsed)

        return result

    def report(self):

        if self.group_errors_by_expectation:
            # This approach is better when I'm developing a grammar,
            # as it tends to group similar cases.

            def err(x): print(x, file=self.f_errors)

            err("%d parsing errors:" % self.error_count)
            err('')
            for (expecting, posns) in sorted(self.error_posns.items()):
                # err('')
                err('X'*80)
                # err('')
                err("Expecting:")
                for e in expecting:
                    err("    %r"  % e)
                for posn in posns:
                    err(shared.source_line_with_caret_marking_column(math.ceil(posn)))

        f = shared.open_for_output(self.file_base + '_prod_counts')
        for prod in self.productions:
            print("%5d %s" % (prod.n_delivered_instances, prod), file=f)

# ------------------------------------------------------------------------------

class Production:
    def __init__(self, lhs_s, rhs_s):
        self.lhs_s = lhs_s
        self.rhs_s = rhs_s

        if 0:
            self.rhs_pieces = [s for s in re.split(r'(%s)' % nt_pattern, rhs_s) if s != '']
        else:
            self.rhs_pieces = []
            # if '-<sub>' in rhs_s: pdb.set_trace()
            p = 0
            for mo in re.finditer(nt_pattern, rhs_s):
                (nt_start, nt_end) = mo.span()
                if p < nt_start:
                    self.rhs_pieces.append(rhs_s[p:nt_start])
                self.rhs_pieces.append(rhs_s[nt_start:nt_end])
                p = nt_end
            if p < len(rhs_s):
                self.rhs_pieces.append(rhs_s[p:])
            # print(self.rhs_pieces)

        if '{EPSILON}' in self.rhs_pieces:
            assert self.rhs_pieces == ['{EPSILON}']
            self.rhs_pieces = []

        # In a GLR parse, there can be lots of reductions
        # that ultimately don't appear in the final parse tree.
        self.n_reductions = 0
        self.n_delivered_instances = 0

    def __str__(self):
        return self.lhs_s + ' : ' + ''.join(self.rhs_pieces)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

nt_pattern = r'\{[A-Z_][A-Z_0-9]*\}'

def convert_grammar_string_to_productions(grammar_string):
    lhs_set = set()
    productions = []
    current_lhs = None
    for line in grammar_string.split('\n'):
        if line == '':
            # blank line
            continue
        elif re.match(r'^ *#', line):
            # comment line
            continue
        elif not line.startswith(' '):
            # lhs
            mo = re.match(f'^({nt_pattern}) :$', line)
            assert mo, line
            current_lhs = mo.group(1)
            assert current_lhs not in lhs_set
            lhs_set.add(current_lhs)
        else:
            # rhs
            productions.append(Production(current_lhs, line.lstrip()))

    # Now that we have all productions,
    # do a consistency check.
    for production in productions:
        for r_item in production.rhs_pieces:
            if re.match(r'^%s$' % nt_pattern, r_item):
                if r_item in ['{_NL}', '{_INDENT}', '{_OUTDENT}']:
                    pass
                else:
                    assert r_item in lhs_set, ("%s looks like a nonterminal but doesn't appear on a LHS" % r_item)
            else:
                compile_regex(r_item)

    return productions

# Because Python's built-in cache isn't big enough.
reo_cache = {}
def compile_regex(regex):
    if regex not in reo_cache:
        reo_cache[regex] = re.compile(regex)
        assert reo_cache[regex].groups <= 1, regex

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class ANode:
    def __init__(self, prod, children, start_posn, end_posn):
        self.prod = prod
        self.children = children
        self.start_posn = int(start_posn)
        self.end_posn = int(end_posn)

    def __repr__(self):
        t = self.source_text()
        if len(t) <= 70:
            return t
        else:
            return t[0:67] + '...'

    def source_text(self):
        return shared.spec_text[self.start_posn:self.end_posn]

    def printTree(self, f=sys.stdout, level=0):
        indentation = '  '*level
        if self.children == []:
            print(indentation + '(' + str(self.prod) + ')', file=f)
        else:
            print(indentation + '(' + str(self.prod), file=f)
            for child in self.children:
                if isinstance(child, str):
                    print(indentation + '  ' + literalize(child), file=f)
                else:
                    child.printTree(f, level+1)
            print(indentation + ')', file=f)

    def is_a(self, lhs_s):
        node = self
        while True:
            if node.prod.lhs_s == lhs_s:
                return node
            elif len(node.children) == 1:
                [child] = node.children
                if isinstance(child, ANode):
                    node = child
                else:
                    return None
            else:
                return None

def literalize(s):
    return (
        '"'
        + s
            .replace('\n', r'\n')
            .replace('"', '""')
        + '"'
    )

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# vim: sw=4 ts=4 expandtab columns=85
