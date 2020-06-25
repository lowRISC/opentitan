// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <sstream>
#include <svdpi.h>
#include <sys/stat.h>
#include <sys/types.h>

// Candidate for hw/dv/verilator/cpp
/**
 * Guard class for SV Scope
 *
 * This guard ensures that all functions in the context where it is instantiated
 * are executed in an SVScope. It will restore the previous scope at destruction
 * and thereby make sure that the previous scope will be restored for all paths
 * that exit the scope.
 */
class SVScoped {
 private:
  svScope prev_scope_ = 0;

 public:
  SVScoped(std::string scopeName) : SVScoped(scopeName.c_str()) {}
  SVScoped(const char *scopeName) : SVScoped(svGetScopeFromName(scopeName)) {}

  SVScoped(svScope scope) { prev_scope_ = svSetScope(scope); }
  ~SVScoped() { svSetScope(prev_scope_); }
};

extern "C" {

extern int simutil_verilator_get_mem(int index, const svBitVecVal *val);
extern int simutil_verilator_set_mem(int index, const svBitVecVal *val);

int run_model(const char *imem_scope, int imem_words, const char *dmem_scope,
              int dmem_words) {
  std::FILE *fp = nullptr;

  char dir[] = "/tmp/otbn_XXXXXX";
  char ifname[] = "/tmp/otbn_XXXXXX/imem";
  char dfname[] = "/tmp/otbn_XXXXXX/dmem";
  char cfname[] = "/tmp/otbn_XXXXXX/cycles";

  if (mkdtemp(dir) == nullptr) {
    std::cerr << "Cannot create temporary directory" << std::endl;
    return 0;
  }

  std::memcpy(ifname, dir, strlen(dir));
  std::memcpy(dfname, dir, strlen(dir));
  std::memcpy(cfname, dir, strlen(dir));

  fp = std::fopen(dfname, "w+");
  if (fp == nullptr) {
    std::cerr << "Cannot open the file " << dfname << std::endl;
    return 0;
  }
  {
    SVScoped scoped(dmem_scope);
    uint8_t buf[32];
    for (size_t w = 0; w < dmem_words; w++) {
      if (!simutil_verilator_get_mem(w, reinterpret_cast<svBitVecVal *>(buf))) {
        std::cerr << "Cannot get dmem @ word " << w << std::endl;
        return 0;
      }
      std::fwrite(buf, 1, 32, fp);
    }
  }
  std::fclose(fp);

  fp = std::fopen(ifname, "w+");
  if (fp == nullptr) {
    std::cerr << "Cannot open the file " << ifname << std::endl;
    return 0;
  }
  {
    SVScoped scoped(imem_scope);
    uint8_t buf[32];
    for (size_t w = 0; w < imem_words; w++) {
      if (!simutil_verilator_get_mem(w, reinterpret_cast<svBitVecVal *>(buf))) {
        std::cerr << "Cannot get imem @ word " << w << std::endl;
        return 0;
      }
      std::fwrite(buf, 1, 4, fp);
    }
  }
  std::fclose(fp);

  std::stringstream strstr;
  strstr << "otbn-python-model " << imem_words << " " << ifname << " "
         << dmem_words << " " << dfname << " " << cfname;

  if (std::system(strstr.str().c_str()) != 0) {
    std::cerr << "Cannot execute model" << std::endl;
    return 0;
  }

  fp = std::fopen(dfname, "r");
  if (fp == nullptr) {
    std::cerr << "Cannot open the file " << dfname << std::endl;
    return 0;
  }

  {
    SVScoped scoped(dmem_scope);
    uint8_t buf[32];
    for (size_t w = 0; w < dmem_words; w++) {
      if (std::fread(buf, 1, 32, fp) != 32) {
        std::cerr << "Cannot read from data memory file" << std::endl;
      }
      if (!simutil_verilator_set_mem(w, reinterpret_cast<svBitVecVal *>(buf))) {
        std::cerr << "Cannot set dmem @ word " << w << std::endl;
        return 0;
      }
    }
  }

  std::fclose(fp);

  int cycles = 0;

  fp = std::fopen(cfname, "r");
  if (fp == nullptr) {
    std::cerr << "Cannot open the file " << cfname << std::endl;
    return 0;
  }

  if (std::fread(&cycles, 4, 1, fp) != 1) {
    std::cerr << "Cannot readback cycles" << std::endl;
    return 0;
  }

  std::fclose(fp);

  return cycles;
}
}
