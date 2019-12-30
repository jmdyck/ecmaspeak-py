
# ecmaspeak-py/DFA.py:
# Deterministic Finite Automaton
# 
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys

from collections import OrderedDict, defaultdict

class Automaton:
    def __init__(self, item0, State_class):
        '''
        item0 must be an 'item' (a state in a Non-deterministic Finite Automaton),
        i.e. an object (stringable and hashable) that defines the method 'each_transition()',
        which yields a sequence of (symbol, item) pairs,
        one for each transition from the item.
        ('symbol' is None for an epsilon transition, and otherwise opaque.)
        '''
        assert hasattr(item0, 'each_transition')
        assert issubclass(State_class, State)

        self.State_class = State_class

        self.state_for_kernel_ = OrderedDict()
        self._open_states = []

        self.start_state = self._ensure_state_for_kernel( [item0], [] )

        while self._open_states:
            state = self._open_states.pop(0)
            if state.should_be_closed():
                state._close()

    def _ensure_state_for_kernel(self, kernel, eg_accessor):
        kernel = tuple(sorted(kernel)) # or frozenset(kernel) ?
        if kernel in self.state_for_kernel_:
            state = self.state_for_kernel_[kernel]
            assert len(state.eg_accessor) <= len(eg_accessor)
            # because we're generating states breadth-first?
        else:
            state_number = len(self.state_for_kernel_)
            state = self.State_class(self, kernel, eg_accessor, state_number)
            self.state_for_kernel_[kernel] = state
            self._open_states.append(state)
        return state

    def print(self, f, stringify_symbol):
        print('Automaton...', file=f)
        for state in self.state_for_kernel_.values():
            state.print(f, stringify_symbol)

class State:
    def __init__(self, automaton, kernel, eg_accessor, number):
        self.automaton = automaton
        self.kernel = kernel
        self.eg_accessor = eg_accessor
        self.number = number
        # if self.number > 0 and self.number % 100 == 0: print('    ', self.number, file=sys.stderr)

    def should_be_closed(self):
        'Subclasses can override.'
        return True

    def _close(self):
        self.items = OrderedDict()
        self._unprocessed_items = []

        for item in self.kernel:
            self._include_item(item)

        self.final_items = []
        self.transition_items = defaultdict(list)
        while self._unprocessed_items:
            item = self._unprocessed_items.pop(0)
            item_is_final = True
            for (symbol,next_item) in item.each_transition():
                item_is_final = False
                if symbol is None:
                    # An epsilon-transition
                    self._include_item(next_item)
                else:
                    # A non-epsilon-transition
                    self.transition_items[symbol].append(next_item)
            if item_is_final:
                self.final_items.append(item)

        self.transitions = {}
        for (symbol, next_items) in sorted(self.transition_items.items()):
            next_state = self.automaton._ensure_state_for_kernel(next_items, self.eg_accessor + [symbol])
            self.transitions[symbol] = next_state

        self.post_close()

    def _include_item(self, item):
        if item not in self.items:
            # print("  adding item", item)
            self.items[item] = True
            self._unprocessed_items.append(item)

    def post_close(self):
        'Subclasses can override.'
        pass

    def print(self, f, stringify_symbol):
        def put(*s): print(*s, file=f)
        #
        put('State #%d' % self.number)
        put('  eg_accessor:', ' '.join(map(stringify_symbol, self.eg_accessor)))
        put('')
        put('  kernel:')
        for item in self.kernel:
            put('    ', item)
        put()

        if not hasattr(self, 'items'):
            # Got False from should_be_closed()
            # (or we're printing while the automaton is being built)
            return

        put('  closure:')
        for item in self.items:
            put('    ', item)
        put()
        put('  final_items:')
        for item in self.final_items:
            put('    ', item)
        put()
        put('  transition_items:')
        for (symbol, items) in sorted(self.transition_items.items()):
            put('    ', stringify_symbol(symbol))
            for item in items:
                put('      ', item)
            put('      -> #%d' % self.transitions[symbol].number)

        self.post_print(put)
        put()

    def post_print(self, put):
        'Subclass can override.'
        pass

# vim: sw=4 ts=4 expandtab
