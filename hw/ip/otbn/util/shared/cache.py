# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Generic, Optional, List, TypeVar

K = TypeVar('K')
V = TypeVar('V')
I = TypeVar('I')

class CacheEntry(Generic[K,V]):
    '''Represents a single entry in a cache.

    The entry must hold two pieces of information:
    - value, the cached result to be returned on a matching lookup
    - key, data needed to determine if the entry matches a lookup (e.g. input
      parameters to the function whose result has been cached)

    Note that this is not a simple key/value store, because a key might match a
    lookup even if it's not an exact match. Determining what exactly needs to
    match is implementation-specific and implemented by subclasses.
    '''
    def __init__(self, key: K, value: V):
        self.key = key
        self.value = value

    def is_match(self, key: K) -> bool:
        '''Returns whether this entry is a match for the key.

        In the simplest case, this could be just self.key == key; however, the
        implementer might choose to ignore certain information when evaluating
        the match, depending on the use-case.
        '''
        raise NotImplementedError()

class Cache(Generic[I,K,V]):
    '''Represents a cache to speed up recursive functions.

    The cache is structured with two layers:
    - The first layer is a dictionary that maps some hashable index type to the
      second layer, a list for each dictionary entry.
    - The second layer is a list of CacheEntry instances to be checked.

    The purpose of the two-layer structure is to speed up lookups; the index
    type should be used to quickly narrow things down to a limited number of
    potentially matching entries (for instance, it could be an input parameter
    to the function that absolutely must match for the cache entries to match).
    '''
    def __init__(self) -> None:
        self.entries : Dict[I,List[CacheEntry[K,V]]] = {}

    def add(self, index: I, entry: CacheEntry[K,V]) -> None:
        # Only add if there's no matching entry already 
        if self.lookup(index, entry.key) is None:
            self.entries.setdefault(index, []).append(entry)

    def lookup(self, index: I, key: K) -> Optional[V]:
        for entry in self.entries.get(index, []):
            if entry.is_match(key):
                return entry.value
        return None
