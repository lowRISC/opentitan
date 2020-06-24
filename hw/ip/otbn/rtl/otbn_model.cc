#include "svdpi.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <sstream>
#include <iostream>
#include <string>
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
  svScope m_prevScope = 0;
  SVScoped() {}

 public:
  SVScoped(std::string scopeName) : SVScoped(scopeName.c_str()) {}
  SVScoped(const char *scopeName) : SVScoped(svGetScopeFromName(scopeName)) {}

  SVScoped(svScope scope) { m_prevScope = svSetScope(scope); }
  ~SVScoped() { svSetScope(m_prevScope); }
};

extern "C" {

extern int simutil_verilator_get_mem(int index, const svBitVecVal *val);
extern int simutil_verilator_set_mem(int index, const svBitVecVal *val);

int run_model(const char *imem_scope, int imem_words, const char *dmem_scope,
              int dmem_words) {
  FILE *ifp = 0;
  FILE *dfp = 0;

  char dir[] = "/tmp/otbn_XXXXXX";
  char ifname[] = "/tmp/otbn_XXXXXX/imem";
  char dfname[] = "/tmp/otbn_XXXXXX/dmem";
  if (mkdtemp(dir) == NULL) {
    std::cerr << "Cannot create temporary directory" << std::endl;
    return -1;
  }

  memcpy(ifname, dir, strlen(dir));
  memcpy(dfname, dir, strlen(dir));

  if(mkfifo(ifname, S_IWUSR | S_IRUSR) != 0) {
    std::cerr << "Cannot create the pipe " << ifname << std::endl;
    return -1;
  }
  if(mkfifo(dfname, S_IWUSR | S_IRUSR) != 0) {
    std::cerr << "Cannot create the pipe " << dfname << std::endl;
    return -1;
  }

  ifp = fopen(ifname, "w+");
  if (!ifp) {
    std::cerr << "Cannot open the pipe " << ifname << std::endl;
    return -1;
  }
  dfp = fopen(dfname, "w+");
  if (!dfp) {
    std::cerr << "Cannot open the pipe " << dfname << std::endl;
    return -1;
  }

  {
    SVScoped scoped(dmem_scope);
    uint8_t buf[32];
    for (size_t w = 0; w < dmem_words; w++) {
      if (!simutil_verilator_get_mem(w, (svBitVecVal *)buf)) {
        std::cerr << "Cannot get dmem @ word " << w << std::endl;
        return -1;
      }
      fwrite(buf, 1, 32, dfp);
    }
  }
  {
    SVScoped scoped(imem_scope);
    uint8_t buf[32];
    for (size_t w = 0; w < imem_words; w++) {
      if (!simutil_verilator_get_mem(w, (svBitVecVal *)buf)) {
        std::cerr << "Cannot get imem @ word " << w << std::endl;
        return -1;
      }
      fwrite(buf, 1, 4, ifp);
    }
  }

  std::stringstream strstr;
  strstr << "otbn-python-model ";
  strstr << imem_words << " " << ifname << " ";
  strstr << dmem_words << " " << dfname;

  system(strstr.str().c_str());

  {
    SVScoped scoped(dmem_scope);
    uint8_t buf[32];
    for (size_t w = 0; w < dmem_words; w++) {
      fread(buf, 1, 32, dfp);
      if (!simutil_verilator_set_mem(w, (svBitVecVal *)buf)) {
        std::cerr << "Cannot set dmem @ word " << w << std::endl;
        return -1;
      }
    }
  }

  fclose(ifp);
  fclose(dfp);

  return 0;
}
}
