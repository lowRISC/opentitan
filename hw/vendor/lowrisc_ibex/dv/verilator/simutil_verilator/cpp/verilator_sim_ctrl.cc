// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilator_sim_ctrl.h"

#include <fcntl.h>
#include <gelf.h>
#include <getopt.h>
#include <libelf.h>
#include <signal.h>
#include <sys/stat.h>
#include <unistd.h>
#include <vltstd/svdpi.h>

#include <iostream>
#include <map>
#include <utility>

// This is defined by Verilator and passed through the command line
#ifndef VM_TRACE
#define VM_TRACE 0
#endif

struct BufferDesc {
  uint8_t *data;
  size_t length;
};

/**
 * Get the current simulation time
 *
 * Called by $time in Verilog, converts to double, to match what SystemC does
 */
double sc_time_stamp() {
  return VerilatorSimCtrl::GetInstance().GetTime();
}

// DPI Exports
extern "C" {

/**
 * Write |file| to a memory
 *
 * @param file path to a SystemVerilog $readmemh()-compatible file (VMEM file)
 */
extern void simutil_verilator_memload(const char *file);

/**
 * Write a 32 bit word |val| to memory at index |index|
 *
 * @return 1 if successful, 0 otherwise
 */
extern int simutil_verilator_set_mem(int index, const svLogicVecVal *val);
}

VerilatorSimCtrl& VerilatorSimCtrl::GetInstance() {
  static VerilatorSimCtrl instance;
  return instance;
}

VerilatorSimCtrl::VerilatorSimCtrl()
    : top_(nullptr),
      time_(0),
      tracing_enabled_(false),
      tracing_enabled_changed_(false),
      tracing_ever_enabled_(false),
      tracing_possible_(VM_TRACE),
      initial_reset_delay_cycles_(2),
      reset_duration_cycles_(2),
      request_stop_(false),
      simulation_success_(true),
      tracer_(VerilatedTracer()),
      term_after_cycles_(0),
      callback_(nullptr) {}

void VerilatorSimCtrl::SetTop(VerilatedToplevel *top, CData *sig_clk,
                              CData *sig_rst,
                              VerilatorSimCtrlFlags flags) {
  top_ = top;
  sig_clk_ = sig_clk;
  sig_rst_ = sig_rst;
  flags_ = flags;
}

int VerilatorSimCtrl::Exec(int argc, char **argv) {
  RegisterSignalHandler();

  bool exit_app = false;
  if (!ParseCommandArgs(argc, argv, exit_app)) {
    return 1;
  }
  if (exit_app) {
    // Successful exit requested by command argument parsing
    return 0;
  }

  RunSimulation();

  if (!WasSimulationSuccessful()) {
    return 1;
  }
  return 0;
}

void VerilatorSimCtrl::RunSimulation() {
  // Print helper message for tracing
  if (TracingPossible()) {
    std::cout << "Tracing can be toggled by sending SIGUSR1 to this process:"
              << std::endl
              << "$ kill -USR1 " << getpid() << std::endl;
  }
  // Run the simulation
  Run();
  // Print simulation speed info
  PrintStatistics();
  // Print helper message for tracing
  if (TracingEverEnabled()) {
    std::cout << std::endl
              << "You can view the simulation traces by calling" << std::endl
              << "$ gtkwave " << GetTraceFileName() << std::endl;
  }
}

void VerilatorSimCtrl::RegisterSignalHandler() {
  struct sigaction sigIntHandler;

  sigIntHandler.sa_handler = SignalHandler;
  sigemptyset(&sigIntHandler.sa_mask);
  sigIntHandler.sa_flags = 0;

  sigaction(SIGINT, &sigIntHandler, NULL);
  sigaction(SIGUSR1, &sigIntHandler, NULL);
}

void VerilatorSimCtrl::SignalHandler(int sig) {
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();

  switch (sig) {
    case SIGINT:
      simctrl.RequestStop(true);
      break;
    case SIGUSR1:
      if (simctrl.TracingEnabled()) {
        simctrl.TraceOff();
      } else {
        simctrl.TraceOn();
      }
      break;
  }
}

void VerilatorSimCtrl::RequestStop(bool simulation_success) {
  request_stop_ = true;
  simulation_success_ &= simulation_success;
}

bool VerilatorSimCtrl::TraceOn() {
  bool old_tracing_enabled = tracing_enabled_;

  tracing_enabled_ = tracing_possible_;
  tracing_ever_enabled_ = tracing_enabled_;

  if (old_tracing_enabled != tracing_enabled_) {
    tracing_enabled_changed_ = true;
  }
  return tracing_enabled_;
}

bool VerilatorSimCtrl::TraceOff() {
  if (tracing_enabled_) {
    tracing_enabled_changed_ = true;
  }
  tracing_enabled_ = false;
  return tracing_enabled_;
}

std::string VerilatorSimCtrl::GetName() const {
  if (top_) {
    return top_->name();
  }
  return "unknown";
}

void VerilatorSimCtrl::PrintHelp() const {
  std::cout << "Execute a simulation model for " << GetName()
            << "\n"
               "\n";
  if (tracing_possible_) {
    std::cout << "-t|--trace\n"
                 "  Write a trace file from the start\n\n";
  }
  std::cout << "-r|--rominit=FILE\n"
               "  Initialize the ROM with FILE (elf/vmem)\n\n"
               "-m|--raminit=FILE\n"
               "  Initialize the RAM with FILE (elf/vmem)\n\n"
               "-f|--flashinit=FILE\n"
               "  Initialize the FLASH with FILE (elf/vmem)\n\n"
               "-l|--meminit=NAME,FILE[,TYPE]\n"
               "  Initialize memory region NAME with FILE [of TYPE]\n"
               "  TYPE is either 'elf' or 'vmem'\n\n"
               "-l list|--meminit=list\n"
               "  Print registered memory regions\n\n"
               "-c|--term-after-cycles=N\n"
               "  Terminate simulation after N cycles\n\n"
               "-h|--help\n"
               "  Show help\n\n"
               "All further arguments are passed to the design and can be used "
               "in the design, e.g. by DPI modules.\n";
}

bool VerilatorSimCtrl::RegisterMemoryArea(const std::string name,
                                          const std::string location) {
  MemArea mem = {.name = name, .location = location};

  auto ret = mem_register_.emplace(name, mem);
  if (ret.second == false) {
    std::cerr << "ERROR: Can not register \"" << name << "\" at: \"" << location
              << "\" (Previously defined at: \"" << ret.first->second.location
              << "\")" << std::endl;
    return false;
  }
  return true;
}

MemImageType VerilatorSimCtrl::GetMemImageTypeByName(const std::string name) {
  if (name.compare("elf") == 0) {
    return kMemImageElf;
  }
  if (name.compare("vmem") == 0) {
    return kMemImageVmem;
  }
  return kMemImageUnknown;
}

MemImageType VerilatorSimCtrl::DetectMemImageType(const std::string filepath) {
  size_t ext_pos = filepath.find_last_of(".");
  std::string ext = filepath.substr(ext_pos + 1);

  if (ext_pos == std::string::npos) {
    // Assume ELF files if no file extension is given.
    // TODO: Make this more robust by actually checking the file contents.
    return kMemImageElf;
  }
  return GetMemImageTypeByName(ext);
}

void VerilatorSimCtrl::PrintMemRegions() const {
  std::cout << "Registered memory regions:" << std::endl;
  for (const auto &m : mem_register_) {
    std::cout << "\t'" << m.second.name << "' at location: '"
              << m.second.location << "'" << std::endl;
  }
}

bool VerilatorSimCtrl::ParseMemArg(std::string mem_argument, std::string &name,
                                   std::string &filepath, MemImageType &type) {
  std::array<std::string, 3> args;
  size_t pos = 0;
  size_t end_pos = 0;
  size_t i;

  for (i = 0; i < 3; ++i) {
    end_pos = mem_argument.find(",", pos);
    // Check for possible exit conditions
    if (pos == end_pos) {
      std::cerr << "ERROR: empty field in: " << mem_argument << std::endl;
      return false;
    }
    if (end_pos == std::string::npos) {
      args[i] = mem_argument.substr(pos);
      break;
    }
    args[i] = mem_argument.substr(pos, end_pos - pos);
    pos = end_pos + 1;
  }
  // mem_argument is not empty as getopt requires an argument,
  // but not a valid argument for memory initialization
  if (i == 0) {
    std::cerr << "ERROR: meminit must be in \"name,file[,type]\""
              << " got: " << mem_argument << std::endl;
    return false;
  }

  name = args[0];
  filepath = args[1];

  if (i == 1) {
    // Type not set explicitly
    type = DetectMemImageType(filepath);
  } else {
    type = GetMemImageTypeByName(args[2]);
  }

  return true;
}

bool VerilatorSimCtrl::MemWrite(const std::string &name,
                                const std::string &filepath) {
  MemImageType type = DetectMemImageType(filepath);
  if (type == kMemImageUnknown) {
    std::cerr << "ERROR: Unable to detect file type for: " << filepath
              << std::endl;
    // Continuing for more error messages
  }
  return MemWrite(name, filepath, type);
}

bool VerilatorSimCtrl::MemWrite(const std::string &name,
                                const std::string &filepath,
                                MemImageType type) {
  // Search for corresponding registered memory based on the name
  auto it = mem_register_.find(name);
  if (it == mem_register_.end()) {
    std::cerr << "ERROR: Memory location not set for: '" << name << "'"
              << std::endl;
    PrintMemRegions();
    return false;
  }

  if (!MemWrite(it->second, filepath, type)) {
    std::cerr << "ERROR: Setting memory '" << name << "' failed." << std::endl;
    return false;
  }
  return true;
}

bool VerilatorSimCtrl::MemWrite(const MemArea &m, const std::string &filepath,
                                MemImageType type) {
  if (!IsFileReadable(filepath)) {
    std::cerr << "ERROR: Memory initialization file "
              << "'" << filepath << "'"
              << " is not readable." << std::endl;
    return false;
  }

  svScope scope = svGetScopeFromName(m.location.data());
  if (!scope) {
    std::cerr << "ERROR: No memory found at " << m.location << std::endl;
    return false;
  }

  switch (type) {
    case kMemImageElf:
      if (!WriteElfToMem(scope, filepath)) {
        std::cerr << "ERROR: Writing ELF file to memory \"" << m.name << "\" ("
                  << m.location << ") failed." << std::endl;
        return false;
      }
      break;
    case kMemImageVmem:
      if (!WriteVmemToMem(scope, filepath)) {
        std::cerr << "ERROR: Writing VMEM file to memory \"" << m.name << "\" ("
                  << m.location << ") failed." << std::endl;
        return false;
      }
      break;
    case kMemImageUnknown:
    default:
      std::cerr << "ERROR: Unknown file type for " << m.name << std::endl;
      return false;
  }
  return true;
}

bool VerilatorSimCtrl::WriteElfToMem(const svScope &scope,
                                     const std::string &filepath) {
  bool retcode;
  svScope prev_scope = svSetScope(scope);

  uint8_t *buf = nullptr;
  size_t len_bytes;

  if (!ElfFileToBinary(filepath, &buf, len_bytes)) {
    std::cerr << "ERROR: Could not load: " << filepath << std::endl;
    retcode = false;
    goto ret;
  }
  for (int i = 0; i < len_bytes / 4; ++i) {
    if (!simutil_verilator_set_mem(i, (svLogicVecVal *)&buf[4 * i])) {
      std::cerr << "ERROR: Could not set memory byte: " << i * 4 << "/"
                << len_bytes << "" << std::endl;

      retcode = false;
      goto ret;
    }
  }

  retcode = true;

ret:
  svSetScope(prev_scope);
  free(buf);
  return retcode;
}

bool VerilatorSimCtrl::WriteVmemToMem(const svScope &scope,
                                      const std::string &filepath) {
  svScope prev_scope = svSetScope(scope);

  // TODO: Add error handling.
  simutil_verilator_memload(filepath.data());

  svSetScope(prev_scope);
  return true;
}

bool VerilatorSimCtrl::ParseCommandArgs(int argc, char **argv, bool &exit_app) {
  const struct option long_options[] = {
      {"rominit", required_argument, nullptr, 'r'},
      {"raminit", required_argument, nullptr, 'm'},
      {"flashinit", required_argument, nullptr, 'f'},
      {"meminit", required_argument, nullptr, 'l'},
      {"term-after-cycles", required_argument, nullptr, 'c'},
      {"trace", no_argument, nullptr, 't'},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

  while (1) {
    int c = getopt_long(argc, argv, ":r:m:f:l:c:th", long_options, nullptr);
    if (c == -1) {
      break;
    }

    // Disable error reporting by getopt
    opterr = 0;

    switch (c) {
      case 0:
        break;
      case 'r':
        if (!MemWrite("rom", optarg)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
        break;
      case 'm':
        if (!MemWrite("ram", optarg)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
        break;
      case 'f':
        if (!MemWrite("flash", optarg)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
        break;
      case 'l': {
        if (strcasecmp(optarg, "list") == 0) {
          PrintMemRegions();
          exit_app = true;
          return true;
        }

        std::string name;
        std::string filepath;
        MemImageType type;
        if (!ParseMemArg(optarg, name, filepath, type)) {
          std::cerr << "ERROR: Unable to parse meminit arguments." << std::endl;
          return false;
        }

        if (!MemWrite(name, filepath, type)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
      } break;
      case 't':
        if (!tracing_possible_) {
          std::cerr << "ERROR: Tracing has not been enabled at compile time."
                    << std::endl;
          return false;
        }
        TraceOn();
        break;
      case 'c':
        term_after_cycles_ = atoi(optarg);
        break;
      case 'h':
        PrintHelp();
        exit_app = true;
        return true;
      case ':':  // missing argument
        std::cerr << "ERROR: Missing argument." << std::endl << std::endl;
        return false;
      case '?':
      default:;
        // Ignore unrecognized options since they might be consumed by
        // Verilator's built-in parsing below.
    }
  }

  Verilated::commandArgs(argc, argv);
  return true;
}

void VerilatorSimCtrl::Trace() {
  // We cannot output a message when calling TraceOn()/TraceOff() as these
  // functions can be called from a signal handler. Instead we print the message
  // here from the main loop.
  if (tracing_enabled_changed_) {
    if (TracingEnabled()) {
      std::cout << "Tracing enabled." << std::endl;
    } else {
      std::cout << "Tracing disabled." << std::endl;
    }
    tracing_enabled_changed_ = false;
  }

  if (!TracingEnabled()) {
    return;
  }

  if (!tracer_.isOpen()) {
    tracer_.open(GetTraceFileName());
    std::cout << "Writing simulation traces to " << GetTraceFileName()
              << std::endl;
  }

  tracer_.dump(GetTime());
}

const char *VerilatorSimCtrl::GetTraceFileName() const {
#ifdef VM_TRACE_FMT_FST
  return "sim.fst";
#else
  return "sim.vcd";
#endif
}

void VerilatorSimCtrl::SetOnClockCallback(SimCtrlCallBack callback) {
  callback_ = callback;
}

void VerilatorSimCtrl::Run() {
  assert(top_ && "Use SetTop() first.");

  // We always need to enable this as tracing can be enabled at runtime
  if (tracing_possible_) {
    Verilated::traceEverOn(true);
    top_->trace(tracer_, 99, 0);
  }

  // Evaluate all initial blocks, including the DPI setup routines
  top_->eval();

  std::cout << std::endl
            << "Simulation running, end by pressing CTRL-c." << std::endl;

  time_begin_ = std::chrono::steady_clock::now();
  UnsetReset();
  Trace();
  while (1) {
    if (time_ >= initial_reset_delay_cycles_ * 2) {
      SetReset();
    }
    if (time_ >= reset_duration_cycles_ * 2 + initial_reset_delay_cycles_ * 2) {
      UnsetReset();
    }

    *sig_clk_ = !*sig_clk_;

    if (*sig_clk_ && (callback_ != nullptr)) {
      callback_(time_);
    }

    top_->eval();
    time_++;

    Trace();

    if (request_stop_) {
      std::cout << "Received stop request, shutting down simulation."
                << std::endl;
      break;
    }
    if (Verilated::gotFinish()) {
      std::cout << "Received $finish() from Verilog, shutting down simulation."
                << std::endl;
      break;
    }
    if (term_after_cycles_ && time_ > term_after_cycles_) {
      std::cout << "Simulation timeout of " << term_after_cycles_
                << " cycles reached, shutting down simulation." << std::endl;
      break;
    }
  }

  top_->final();
  time_end_ = std::chrono::steady_clock::now();

  if (TracingEverEnabled()) {
    tracer_.close();
  }
}

void VerilatorSimCtrl::SetReset() {
  if (flags_ & ResetPolarityNegative) {
    *sig_rst_ = 0;
  } else {
    *sig_rst_ = 1;
  }
}

void VerilatorSimCtrl::UnsetReset() {
  if (flags_ & ResetPolarityNegative) {
    *sig_rst_ = 1;
  } else {
    *sig_rst_ = 0;
  }
}

void VerilatorSimCtrl::SetInitialResetDelay(unsigned int cycles) {
  initial_reset_delay_cycles_ = cycles;
}

void VerilatorSimCtrl::SetResetDuration(unsigned int cycles) {
  reset_duration_cycles_ = cycles;
}

bool VerilatorSimCtrl::IsFileReadable(std::string filepath) const {
  struct stat statbuf;
  return stat(filepath.data(), &statbuf) == 0;
}

bool VerilatorSimCtrl::FileSize(std::string filepath, int &size_byte) const {
  struct stat statbuf;
  if (stat(filepath.data(), &statbuf) != 0) {
    size_byte = 0;
    return false;
  }

  size_byte = statbuf.st_size;
  return true;
}

unsigned int VerilatorSimCtrl::GetExecutionTimeMs() const {
  return std::chrono::duration_cast<std::chrono::milliseconds>(time_end_ -
                                                               time_begin_)
      .count();
}

void VerilatorSimCtrl::PrintStatistics() const {
  double speed_hz = time_ / 2 / (GetExecutionTimeMs() / 1000.0);
  double speed_khz = speed_hz / 1000.0;

  std::cout << std::endl
            << "Simulation statistics" << std::endl
            << "=====================" << std::endl
            << "Executed cycles:  " << time_ / 2 << std::endl
            << "Wallclock time:   " << GetExecutionTimeMs() / 1000.0 << " s"
            << std::endl
            << "Simulation speed: " << speed_hz << " cycles/s "
            << "(" << speed_khz << " kHz)" << std::endl;

  int trace_size_byte;
  if (tracing_enabled_ && FileSize(GetTraceFileName(), trace_size_byte)) {
    std::cout << "Trace file size:  " << trace_size_byte << " B" << std::endl;
  }
}

bool VerilatorSimCtrl::ElfFileToBinary(const std::string &filepath,
                                       uint8_t **data,
                                       size_t &len_bytes) const {
  bool retval;
  std::list<BufferDesc> buffers;
  size_t offset = 0;
  (void)elf_errno();
  len_bytes = 0;

  if (elf_version(EV_CURRENT) == EV_NONE) {
    std::cerr << elf_errmsg(-1) << std::endl;
    return false;
  }

  int fd = open(filepath.c_str(), O_RDONLY, 0);
  if (fd < 0) {
    std::cerr << "Could not open file: " << filepath << std::endl;
    return false;
  }

  Elf *elf_desc;
  elf_desc = elf_begin(fd, ELF_C_READ, NULL);
  if (elf_desc == NULL) {
    std::cerr << elf_errmsg(-1) << " in: " << filepath << std::endl;
    retval = false;
    goto return_fd_end;
  }
  if (elf_kind(elf_desc) != ELF_K_ELF) {
    std::cerr << "Not a ELF file: " << filepath << std::endl;
    retval = false;
    goto return_elf_end;
  }
  // TODO: add support for ELFCLASS64
  if (gelf_getclass(elf_desc) != ELFCLASS32) {
    std::cerr << "Not a 32-bit ELF file: " << filepath << std::endl;
    retval = false;
    goto return_elf_end;
  }

  size_t phnum;
  if (elf_getphdrnum(elf_desc, &phnum) != 0) {
    std::cerr << elf_errmsg(-1) << " in: " << filepath << std::endl;
    retval = false;
    goto return_elf_end;
  }

  GElf_Phdr phdr;
  Elf_Data *elf_data;
  elf_data = NULL;
  for (size_t i = 0; i < phnum; i++) {
    if (gelf_getphdr(elf_desc, i, &phdr) == NULL) {
      std::cerr << elf_errmsg(-1) << " segment number: " << i
                << " in: " << filepath << std::endl;
      retval = false;
      goto return_elf_end;
    }
    if (phdr.p_type != PT_LOAD) {
      std::cout << "Program header number " << i << "is not of type PT_LOAD."
                << "Continue." << std::endl;
      continue;
    }
    elf_data = elf_getdata_rawchunk(elf_desc, phdr.p_offset, phdr.p_filesz,
                                    ELF_T_BYTE);

    if (elf_data == NULL) {
      retval = false;
      goto return_elf_end;
    }

    BufferDesc buf_data;
    buf_data.length = elf_data->d_size;
    len_bytes += buf_data.length;
    buf_data.data = (uint8_t *)malloc(elf_data->d_size);
    memcpy(buf_data.data, ((uint8_t *)elf_data->d_buf), buf_data.length);
    buffers.push_back(buf_data);
  }

  // TODO: Check for the case that phdr.p_memsz > phdr.p_filesz

  // Put the collected data into a continuous buffer
  // Memory is freed by the caller
  *data = (uint8_t *)malloc(len_bytes);
  for (std::list<BufferDesc>::iterator it = buffers.begin();
       it != buffers.end(); ++it) {
    memcpy(((uint8_t *)*data) + offset, it->data, it->length);
    offset += it->length;
    free(it->data);
  }
  buffers.clear();

  retval = true;

return_elf_end:
  elf_end(elf_desc);
return_fd_end:
  close(fd);
  return retval;
}
