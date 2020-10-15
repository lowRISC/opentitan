// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

// Utility class representing disjoint segments of memory

#include <cassert>
#include <map>

// The type used to represent address ranges. This is essentially a std::pair,
// but we need a operator< custom for the internal map.
template <typename addr_t>
struct AddrRange {
  addr_t lo, hi;
};

template <typename addr_t>
bool operator<(const AddrRange<addr_t> &a, const AddrRange<addr_t> &b) {
  return a.lo < b.lo;
}

template <typename addr_t, typename val_t>
class RangedMap {
 public:
  using rng_t = AddrRange<addr_t>;

  // Try to insert an entry that covers the address range [min_addr, max_addr]
  // (inclusive) with value val.
  //
  // If there is an existing entry that overlaps with the range on either side,
  // the map and val are unchanged and a pointer to the existing entry is
  // returned. Otherwise, returns nullptr.
  const val_t *EmplaceDisjoint(addr_t min_addr, addr_t max_addr, val_t &&val) {
    assert(min_addr <= max_addr);
    rng_t rng = {.lo = min_addr, .hi = max_addr};

    if (!map_.empty()) {
      // We start by checking for an overlap "from the right". This would be a
      // region that starts strictly above min_addr, but where it's low address
      // is still <= max_addr. We can use std::map::upper_bound to find the
      // first region strictly above min_addr (which returns the end iterator
      // if there isn't one).
      auto right_it = map_.upper_bound(rng);
      if (right_it != map_.end()) {
        addr_t right_min = right_it->first.lo;
        if (right_min <= max_addr) {
          return &right_it->second;
        }
      }

      // We also need to check from the left side. This would be a region that
      // starts at or before min_addr and extends past it. If right_it is
      // mem_.begin(), there is no such region (because the lowest addressed
      // region already starts above min_addr). Otherwise, decrement right_it
      // to get the highest addressed region that starts at or before min_addr.
      // Note this still works if right_it is the end iterator: we just pick up
      // the last region, which we know exists because map_ is not empty.
      if (right_it != map_.begin()) {
        auto left_it = std::prev(right_it);
        addr_t left_max = left_it->first.hi;

        if (min_addr <= left_max) {
          return &left_it->second;
        }
      }
    }

    // Phew, no overlap!
    map_.insert(std::make_pair(rng, std::move(val)));
    return nullptr;
  }

  // Try to find an entry hitting the given address. Returns nullptr if there
  // is none.
  const val_t *Find(addr_t addr) const {
    // To find the entry containing addr, use upper_bound to find the first
    // region strictly after it, and then std::prev to step backwards. This
    // fails if either the map is empty (obviously!) or if ub_it is already the
    // beginning of the map.
    if (map_.empty())
      return nullptr;

    rng_t diag = {.lo = addr, .hi = addr};
    auto it = map_.upper_bound(diag);
    if (it == map_.begin())
      return nullptr;

    --it;

    // At this point, it will point at the right region if there is one. We
    // know that it->first.lo <= addr (because of how upper_bound works). We
    // now just need to check that addr <= it->first.hi.
    return (addr <= it->first.hi) ? &it->second : nullptr;
  }

 private:
  std::map<rng_t, val_t> map_;
};
