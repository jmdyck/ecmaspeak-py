# ecmaspeak-py/DecoratedFuncDict.py:
# A useful dict variant.
#
# Copyright (C) 2019  J. Michael Dyck <jmdyck@ibiblio.org>

class DecoratedFuncDict:
    '''
    This differs from a standard dict in the following ways:

     -- `foo[key] = func` (where `foo` is an instance of this class,
        and `func` is a function) can also be accomplished by preceding
        the declaration of `func` with the decoration `@foo.put(key)`

     -- Attempting to overwrite an existing entry raises an exception.

     -- It keeps track of the number of times each entry is accessed,
        which you can get via the 'access_counts' method.
    '''
    def __init__(self):
        self._funcs = {}
        self._access_counts = {}
        # Rather than 2 separate dicts,
        # could have a single dict to store both func and access_count,
        # either in an object or a tuple.

    def put(self, key):
        def decorator(func):
            self[key] = func
            return func
        return decorator

    def __setitem__(self, key, func):
        assert key not in self._funcs
        self._funcs[key] = func
        self._access_counts[key] = 0

    def __contains__(self, key):
        return (key in self._funcs)

    def __getitem__(self, key):
        f = self._funcs[key]
        self._access_counts[key] += 1
        return f

    def access_counts(self):
        return self._access_counts.items()

# vim: sw=4 ts=4 expandtab
