// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <map>
#include <string>
#include <svdpi.h>
#include <vector>

#include "ranged_map.h"

enum MemImageType {
  kMemImageUnknown = 0,
  kMemImageElf,
  kMemImageVmem,
};

// The "load" location of a memory area. base is the lowest address in
// the area, and should correspond to an ELF file's LMA. size is the
// length of the area in bytes.
struct MemAreaLoc {
  uint32_t base;
  uint32_t size;
};

struct MemArea {
  std::string name;      // Unique identifier
  std::string location;  // Design scope location
  uint32_t width_byte;   // Memory width in bytes
  MemAreaLoc addr_loc;   // Address location. If !size, location is unknown.
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
  /**
   * Register a memory as instantiated by generic ram
   *
   * The |name| must be a unique identifier. The function will return false if
   * |name| is already used. |location| is the path to the scope of the
   * instantiated memory, which needs to support the DPI-C interfaces
   * 'simutil_memload' and 'simutil_set_mem' used for 'vmem' and 'elf' files,
   * respectively.
   *
   * The |width_bit| argument specifies the with in bits of the target memory
   * instance (used for packing data). This must be a multiple of 8. If
   * |addr_loc| is not null, it gives the base and size of the memory for
   * loading in the address space (corresponding to LMAs in an ELF file).
   *
   * Memories must be registered before command arguments are parsed by
   * ParseCommandArgs() in order for them to be known.
   */
  bool RegisterMemoryArea(const std::string name, const std::string location,
                          size_t width_bit, const MemAreaLoc *addr_loc);

  /**
   * Register a memory with default width (32bits)
   */
  bool RegisterMemoryArea(const std::string name, const std::string location);

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

 private:
  // Memory area registry
  std::map<std::string, MemArea> name_to_mem_;
  RangedMap<uint32_t, MemArea *> addr_to_mem_;

  // Staging area, loaded by StageElf. The map is keyed by names of memories
  // stored in name_to_mem_. We also ensure that every segment in a StagedMem
  // for a memory starts at an address that's aligned for the word width of
  // that memory. Note: we don't also check segments' lengths are aligned.
  std::map<std::string, StagedMem> staging_area_;
  const StagedMem empty_;

  /**
   * Find a region containing for the given segment's addresses.
   * Raises a std::exception if none is found.
   */
  const MemArea &GetRegionForSegment(const std::string &path, int seg_idx,
                                     uint32_t lma, uint32_t mem_sz) const;
};
