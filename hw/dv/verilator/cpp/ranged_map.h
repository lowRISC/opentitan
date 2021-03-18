// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_RANGED_MAP_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_RANGED_MAP_H_

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

  // A function used to merge overlapping segments. When called by
  // Emplace(), val1 will be the newer value and val0 will be the
  // older.
  typedef val_t (*MergeFun)(const rng_t &rng0, val_t &&val0, const rng_t &rng1,
                            val_t &&val1);

  // Insert an entry that covers the address range [min_addr, max_addr]
  // (inclusive) with value val.
  void Emplace(addr_t min_addr, addr_t max_addr, val_t &&new_val,
               MergeFun merge) {
    assert(min_addr <= max_addr);

    // Construct hit_lo / hit_hi, a pair of iterators that bound the
    // segments that touch the new value.
    auto hit_lo = map_.end();
    auto hit_hi = map_.end();

    rng_t rng = {.lo = min_addr, .hi = max_addr};

    if (!map_.empty()) {
      // Start by finding the first region that starts strictly above min_addr.
      auto right_it = map_.upper_bound(rng);
      hit_hi = right_it;

      // If hit_hi is map_.end(), every region starts at or below min_addr. If
      // not, the region it points to overlaps with the range if hit_hi->first
      // <= max_addr. Increment hit_hi until we get to the end or are no longer
      // overlapping. The result is the end iterator for our range.
      while (hit_hi != map_.end() && hit_hi->first.lo <= max_addr) {
        ++hit_hi;
      }

      // Now we need to find the low end of the range. Start at right_it and
      // decrement while we've not got to the beginning and while the previous
      // iterator has a top >= min_addr.
      hit_lo = right_it;
      while (hit_lo != map_.begin() &&
             min_addr <= std::prev(hit_lo)->first.hi) {
        --hit_lo;
      }
    }

    // The entry is disjoint from all others iff hit_lo == hit_hi. In which
    // case, we can just insert it.
    if (hit_lo == hit_hi) {
      map_.insert(std::make_pair(rng, std::move(new_val)));
      return;
    }

    // Otherwise, we use the merge function to merge everything together.
    // Accumulate into a new val_t and update min_addr / max_addr as we go.
    // Peel off the 1st iteration of the loop to avoid an unnecessary move/copy
    // of new_val.
    val_t acc = merge(hit_lo->first, std::move(hit_lo->second), rng,
                      std::move(new_val));
    min_addr = std::min(min_addr, hit_lo->first.lo);
    max_addr = std::max(max_addr, hit_lo->first.hi);

    for (auto it = std::next(hit_lo); it != hit_hi; ++it) {
      rng_t rng1 = {.lo = min_addr, .hi = max_addr};
      acc = merge(it->first, std::move(it->second), rng1, std::move(acc));
      min_addr = std::min(min_addr, it->first.lo);
      max_addr = std::max(max_addr, it->first.hi);
    }

    // We've merged everything, and have possibly trashed the values pointed to
    // by all the iterators in the range. Throw that lot away and finally
    // insert the merged result.
    map_.erase(hit_lo, hit_hi);
    rng_t rng1 = {.lo = min_addr, .hi = max_addr};
    map_.insert(std::make_pair(rng1, std::move(acc)));
  }

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

  // Iteration interface
  using map_t = std::map<rng_t, val_t>;
  using const_iterator = typename map_t::const_iterator;

  const_iterator begin() const { return const_iterator(map_.begin()); }
  const_iterator end() const { return const_iterator(map_.end()); }
  size_t size() const { return map_.size(); }

  // Try to find an entry hitting the given address. Returns end() if there is
  // none.
  const_iterator find(addr_t addr) const {
    // To find the entry containing addr, use upper_bound to find the first
    // region strictly after it, and then std::prev to step backwards. This
    // fails if either the map is empty (obviously!) or if ub_it is already the
    // beginning of the map.
    if (map_.empty())
      return end();

    rng_t diag = {.lo = addr, .hi = addr};
    auto it = map_.upper_bound(diag);
    if (it == map_.begin())
      return end();

    --it;

    // At this point, it will point at the right region if there is one. We
    // know that it->first.lo <= addr (because of how upper_bound works). We
    // now just need to check that addr <= it->first.hi.
    return (addr <= it->first.hi) ? const_iterator(it) : end();
  }

 private:
  std::map<rng_t, val_t> map_;
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_RANGED_MAP_H_
