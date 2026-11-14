// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A model of the data in an RRAM partition
//
// This is fundamentally a big array of RRAM words (like the model in ../../../../rram_macro), but
// it also maintains a "dirty array" which has a counter of the number of accesses currently in
// flight that touch a word.
//
// Maintaining this array lets a scoreboard avoid edge conditions caused by operations that overlap.

class rram_partition_model extends uvm_component;
  `uvm_component_utils(rram_partition_model)

  // The model maintained by the class for a single RRAM word
  typedef struct {
    // The modelled value of the word. If known is true and dirty_count is zero, this is believed to
    // be the value of the word in RRAM.
    bit [DataWidth-1:0] value;

    // The current "generation" for this word. This starts at zero and is incremented on every write
    // that changes the value. A check to make sure that a read has returned the right value should:
    //
    //  - Get the generation when the read is started.
    //  - Get the stored value and also the generation when the read finishes.
    //  - If the two generations are equal, the word was constant through the period (and so the
    //    read should have returned the modelled value.
    int unsigned generation;

    // The number of write operations that have been started on the word and haven't yet completed.
    // If this is nonzero, the word's value is not considered to be known.
    int unsigned pending_count;

    // True if the word's value is known (modulo any pending operation tracked in pending_count).
    bit          known;
  } word_model_t;

  // The size of the partition, measured in RRAM words. Set this with set_size() before this
  // component's build_phase.
  local int unsigned m_size_words;

  // The array giving a model of words in the partition. Created in build_phase.
  local word_model_t m_words[];

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);

  // Set the size of the partition, measured in RRAM words. Call this before build_phase.
  extern function void set_size_words(int unsigned size_words);

  // Take a snapshot of the partition contents using a mem_bkdr_util.
  extern function void take_backdoor_snapshot(mem_bkdr_util bkdr_util);

  // Called at the end of reset. Clear every word's pending_count.
  extern function void end_of_reset();

  // Start a write operation on a word in the array
  extern function void start_write_operation(int unsigned word_idx);

  // Complete a write operation on a word in the array. If this is the last pending write operation
  // on the word, the known flag is set.
  extern function void complete_write_operation(int unsigned word_idx, bit [DataWidth-1:0] value);

  // End a write operation on a word in the array, but without considering the word value to have
  // been set. Unlike complete_write_operation, this doesn't set the known flag.
  extern function void abort_write_operation(int unsigned word_idx);

  // Get the generation of a word in the array
  extern function int unsigned get_generation(int unsigned word_idx);

  // Get whether a RRAM word in the array has a known value
  extern function bit get_known(int unsigned word_idx);

  // Get the modelled value of a 128-bit word in the array.
  extern function bit [DataWidth-1:0] get_value(int unsigned word_idx);

  // Check an RRAM word exists
  extern local function void check_word_exists(int unsigned word_idx, string action);

  // The core of ending a write operation on a word in the array (shared by complete_write_operation
  // and abort_write_operation).
  extern local function void end_write_operation(int unsigned word_idx);

  // Set the value of a word in the array (because of a backdoor read)
  extern local function void set_word_directly(int unsigned word_idx, bit [DataWidth-1:0] value);
endclass

function rram_partition_model::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void rram_partition_model::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (m_size_words == 0) begin
    `uvm_fatal("no_size", "set_size_words() was not called before build_phase.")
  end

  m_words = new[m_size_words];
endfunction

function void rram_partition_model::set_size_words(int unsigned size_words);
  if (size_words == 0) `uvm_fatal("empty_size", "Cannot set m_size_words to zero.")
  if (m_size_words > 0) `uvm_fatal("resetting_size", "Cannot set m_size_words a second time.")

  m_size_words = size_words;
endfunction

function void rram_partition_model::take_backdoor_snapshot(mem_bkdr_util bkdr_util);
  int unsigned bus_words_per_word = DataWidth / 32;

  if (m_words.size() == 0) `uvm_fatal("no_words", "The m_words model is not yet created.")

  // Check that the backdoor utility is wrapping a memory area large enough
  if (bkdr_util.get_size_bytes() < m_words.size() * (DataWidth / 8)) begin
    `uvm_fatal("small_bkdr",
               $sformatf("The backdoor utility is %0d bytes long, but the model expects %0d.",
                         bkdr_util.get_size_bytes(), m_words.size() * (DataWidth / 8)))
  end

  for (int unsigned i = 0; i < m_words.size(); i++) begin
    logic [DataWidth-1:0] raw_val;

    // Don't bother loading the word if there's a write pending: we'll overwrite it shortly anyway.
    if (m_words[i].pending_count != 0) continue;

    for (int unsigned j = 0; j < bus_words_per_word; j++) begin
      raw_val[j * 32 +: 32] = bkdr_util.read32(4 * (bus_words_per_word * i + j));
    end
    if (!$isunknown(raw_val)) begin
      m_words[i].value = raw_val;
      m_words[i].generation++;
      m_words[i].known = 1;
    end
  end
endfunction

function void rram_partition_model::end_of_reset();
  for (int unsigned i = 0; i < m_words.size(); i++) m_words[i].pending_count = 0;
endfunction

function void rram_partition_model::start_write_operation(int unsigned word_idx);
  if (m_words.size() == 0) `uvm_fatal("not_built", "m_words is empty, so build_phase has not run.")
  if (word_idx >= m_words.size()) begin
    `uvm_fatal("invalid_idx",
               $sformatf("Cannot start write operation on word %0d: m_words only has %0d elements.",
                         word_idx, m_words.size()))
  end

  m_words[word_idx].pending_count++;
  m_words[word_idx].known = 0;
endfunction

function void rram_partition_model::complete_write_operation(int unsigned        word_idx,
                                                             bit [DataWidth-1:0] value);
  end_write_operation(word_idx);
  if (!m_words[word_idx].pending_count) begin
    m_words[word_idx].value = value;
    m_words[word_idx].generation++;
    m_words[word_idx].known = 1;
  end
endfunction

function void rram_partition_model::abort_write_operation(int unsigned word_idx);
  end_write_operation(word_idx);
endfunction

function int unsigned rram_partition_model::get_generation(int unsigned word_idx);
  check_word_exists(word_idx, "get generation");
  return m_words[word_idx].generation;
endfunction

function bit rram_partition_model::get_known(int unsigned word_idx);
  check_word_exists(word_idx, "get known");
  return m_words[word_idx].known;
endfunction

function bit [DataWidth-1:0] rram_partition_model::get_value(int unsigned word_idx);
  check_word_exists(word_idx, "get value");
  return m_words[word_idx].value;
endfunction

function void rram_partition_model::check_word_exists(int unsigned word_idx, string action);
  if (m_words.size() == 0) begin
    `uvm_fatal("not_built",
               $sformatf("Cannot %0s. m_words is empty, so build_phase has not run.", action))
  end
  if (word_idx >= m_words.size()) begin
    `uvm_fatal("invalid_idx",
               $sformatf("Cannot %0s for word %0d: m_words only has %0d elements.",
                         action, word_idx, m_words.size()))
  end
endfunction

function void rram_partition_model::end_write_operation(int unsigned word_idx);
  check_word_exists(word_idx, "end write operation");
  if (m_words[word_idx].pending_count == 0) begin
    `uvm_fatal("unstarted_op",
               $sformatf("Cannot end write operation on word %0d: there is none in progress.",
                         word_idx))
  end

  m_words[word_idx].pending_count--;
endfunction

function void rram_partition_model::set_word_directly(int unsigned        word_idx,
                                                      bit [DataWidth-1:0] value);
  check_word_exists(word_idx, "directly set value");

  m_words[word_idx].value = value;
  if (m_words[word_idx].pending_count == 0) m_words[word_idx].known = 1;
endfunction
