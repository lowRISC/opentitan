// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_DPI_MEMUTIL_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_DPI_MEMUTIL_H_

#include <map>
#include <memory>
#include <string>
#include <svdpi.h>
#include <vector>

#include "mem_area.h"
#include "ranged_map.h"

// Forward declaration for the Elf type from libelf.
struct Elf;

enum MemImageType {
  kMemImageUnknown = 0,
  kMemImageElf,
  kMemImageVmem,
};

// Staged data for a given memory area.
//
// This is represented as an ordered list of disjoint segments (as loaded from
// an ELF file).
//
// Once it is nonempty, the class maintains the invariant that min_addr_ /
// max_addr_ is the smallest / largest byte offset with valid data.
class StagedMem {
 public:
  StagedMem() : min_addr_(~(uint32_t)0), max_addr_(0) {}

  // Add a segment to the tracked memory
  void AddSegment(uint32_t offset, std::vector<uint8_t> &&seg);

  // Glob together the tracked segments, interspersing them with
  // zeros, and return as a single flat array.
  std::vector<uint8_t> GetFlat() const;

  typedef RangedMap<uint32_t, std::vector<uint8_t>> SegMap;

  std::pair<uint32_t, uint32_t> GetBounds() const {
    return std::make_pair(min_addr_, max_addr_);
  }
  const SegMap &GetSegs() const { return segs_; }

 private:
  uint32_t min_addr_, max_addr_;
  SegMap segs_;
};

/**
 * Provide various memory loading utilities for verilog simulations
 *
 * These utilities require the corresponding DPI functions:
 * simutil_memload()
 * simutil_set_mem()
 * to be defined somewhere as SystemVerilog functions.
 */
class DpiMemUtil {
 public:
  virtual ~DpiMemUtil() {}

  /**
   * Register a memory as instantiated by generic ram
   *
   * The |name| must be a unique identifier. The constructor will
   * throw a std::runtime_error if |name| is already used.
   *
   * |base| gives the base address of the memory in a logical address
   * space that corresponds to LMAs in an ELF file. If this overlaps
   * with some other registered memory, the constructor throws a
   * std::runtime_error.
   *
   * The |mem_area| argument describes the memory area to be registered and
   * must not be null. This function does not take ownership of the object,
   * which must survive at least as long as the DpiMemutil object.
   *
   * Memories must be registered before command arguments are parsed by
   * ParseCommandArgs() in order for them to be known.
   */
  void RegisterMemoryArea(const std::string &name, uint32_t base,
                          const MemArea *mem_area);

  /**
   * Guess the type of the file at |path|.
   *
   * If |type| is non-null, it is the name of an image type and will be used.
   * Otherwise, the check is based on |path|. If |type| is not a valid name or
   * if the function can't guess from the path, throws a std::runtime_error
   * with a message about what went wrong.
   *
   * Never returns kMemImageUnknown.
   */
  static MemImageType GetMemImageType(const std::string &path,
                                      const char *type);

  /**
   * Print a list of all registered memory regions
   *
   * @see RegisterMemoryArea()
   */
  void PrintMemRegions() const;

  /**
   * Load the file at filepath into the named memory. If type is
   * kMemImageUnknown, the file type is determined from the path.
   */
  void LoadFileToNamedMem(bool verbose, const std::string &name,
                          const std::string &filepath, MemImageType type);

  /**
   * Load an ELF file, placing segments in memories by LMA.
   *
   * Replaces any data currently in the staging area.
   */
  void LoadElfToMemories(bool verbose, const std::string &filepath);

  /**
   * Load an ELF file into a staging area in this object, which can then be
   * accessed with GetMemoryData().
   *
   * If the load fails, raises a std::exception with information about what
   * happened.
   */
  void StageElf(bool verbose, const std::string &path);

  /**
   * Get the contents of the staging area by memory name
   */
  const StagedMem &GetMemoryData(const std::string &mem_name) const;

 protected:
  /**
   * A hook for subclasses to do extra computations with loaded ELF data. This
   * runs as part of StageElf: after loading the ELF file, but before reading
   * in the segments.
   */
  virtual void OnElfLoaded(Elf *elf_file) {}

 private:
  // Memory area registry. The maps give indices pointing into the vectors
  // (which all have the same number of elements). Note that mem_areas_ does
  // not own the objects that it points to.
  std::vector<const MemArea *> mem_areas_;
  std::vector<uint32_t> base_addrs_;
  std::vector<std::string> names_;

  std::map<std::string, size_t> name_to_mem_;
  RangedMap<uint32_t, size_t> addr_to_mem_;

  // Staging area, loaded by StageElf. The map is keyed by names of memories
  // stored in name_to_mem_. We also ensure that every segment in a StagedMem
  // for a memory starts at an address that's aligned for the word width of
  // that memory. Note: we don't also check segments' lengths are aligned.
  std::map<std::string, StagedMem> staging_area_;
  const StagedMem empty_;

  /**
   * Find the index of a memory area containing the given segment's addresses.
   * Raises a std::exception if none is found.
   */
  size_t GetRegionForSegment(const std::string &path, int seg_idx, uint32_t lma,
                             uint32_t mem_sz) const;
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_DPI_MEMUTIL_H_
