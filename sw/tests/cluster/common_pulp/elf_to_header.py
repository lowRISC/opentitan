#!/usr/bin/env python3

#
# Copyright (C) 2018 ETH Zurich, University of Bologna
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

from elftools.elf.elffile import ELFFile
import os
import os.path
import struct
import argparse

c_header = """\
// Auto-generated code
#ifdef USE_HYPER
#include "hyperbus_test.h"
#endif

extern int __cluster_code_start;
extern int __cluster_code_end;

"""
c_function = """\
   #ifdef CLUSTER_BIN 
      uint32_t *p, *end, *p0;
      p = (uint32_t*)&__cluster_code_start;
      p0 = (uint32_t*)&__cluster_code_start;
      end = (uint32_t*)&__cluster_code_end;
       #ifdef USE_HYPER
         udma_hyper_setup();
         set_pagebound_hyper(2048);
         udma_hyper_dread((end-p)*4,p-0x80000000, 0x1C000000, 128, 0);
         udma_hyper_wait(0);
       #else
         uint32_t *addr = (uint32_t*) 0x1C000100;
         for (uint32_t i = 0; i < (end-p0) >> 2; i++) {
          pulp_write32(addr + 0, pulp_read32(p + 0));
          pulp_write32(addr + 1, pulp_read32(p + 1));
          pulp_write32(addr + 2, pulp_read32(p + 2));
          pulp_write32(addr + 3, pulp_read32(p + 3));
          addr += 4;
          p += 4;
         }
         while(p < end) {
          pulp_write32(addr++,pulp_read32(p++));
         }
       #endif
  #else
"""

class stim(object):


  def __init__(self, verbose=False):
    self.binaries = []
    self.mem = {}
    self.verbose = verbose
    self.areas = []

    self.dump('Created stimuli generator')

  def get_entry(self):
    with open(self.binaries[0], 'rb') as file:
        elffile = ELFFile(file)
        return elffile.header['e_entry']

  def dump(self, str):
    if self.verbose:
      print (str)

  def add_binary(self, binary):
    self.dump('  Added binary: %s' % binary)
    self.binaries.append(binary)

  def add_area(self, start, size):
    self.dump('  Added target area: [0x%x -> 0x%x]' % (start, start + size))
    self.areas.append([start, start+size])


  def __add_mem_word(self, base, size, data, width):

    aligned_base = base & ~(width - 1)

    shift = base - aligned_base
    iter_size = width - shift
    if iter_size > size:
      iter_size = size

    value = self.mem.get(str(aligned_base))
    if value is None:
      value = 0

    value &= ~(((1<<width) - 1) << (shift*8))
    value |= int.from_bytes(data[0:iter_size], byteorder='little') << (shift*8)

    self.mem[str(aligned_base)] = value

    return iter_size





  def __add_mem(self, base, size, data, width):

    while size > 0:

      iter_size = self.__add_mem_word(base, size, data, width)

      size -= iter_size
      base += iter_size
      data = data[iter_size:]


  def __gen_stim_slm(self, filename, width):

    self.dump('  Generating to file: ' + filename)

    try:
      os.makedirs(os.path.dirname(filename))
    except:
      pass

    with open(filename, 'w') as file:
      for key in sorted(self.mem.keys()):
        file.write('%X_%0*X\n' % (int(key), width*2, self.mem.get(key)))

  def __gen_stim_header(self, filename, width):

    self.dump('  Generating to file: ' + filename)

    try:
      os.makedirs(os.path.dirname(filename))
    except:
      pass

    with open(filename, 'w') as file:
      file.write(c_header)
      file.write('int load_cluster_code() {\n' )
      file.write(c_function)
      for key in sorted(self.mem.keys()):
        if int(key) > 0x1c000000:
          file.write('  (*(volatile unsigned int *)(long)(0x%X)) = 0x%0*X ;\n' % (int(key), width*2, self.mem.get(key)))
      file.write('#endif\n')
      file.write('return 0; \n }\n')
                 
            
  def __parse_binaries(self, width):

    self.mem = {}

    for binary in self.binaries:

        with open(binary, 'rb') as file:
            elffile = ELFFile(file)

            for segment in elffile.iter_segments():

                if segment['p_type'] == 'PT_LOAD':

                    data = segment.data()
                    addr = segment['p_paddr']
                    size = len(data)

                    load = True
                    if len(self.areas) != 0:
                      load = False
                      for area in self.areas:
                        if addr >= area[0] and addr + size <= area[1]:
                          load = True
                          break

                    if load:

                      self.dump('  Handling section (base: 0x%x, size: 0x%x)' % (addr, size))

                      self.__add_mem(addr, size, data, width)

                      if segment['p_filesz'] < segment['p_memsz']:
                          addr = segment['p_paddr'] + segment['p_filesz']
                          size = segment['p_memsz'] - segment['p_filesz']
                          self.dump('  Init section to 0 (base: 0x%x, size: 0x%x)' % (addr, size))
                          self.__add_mem(addr, size, [0] * size, width)

                    else:

                      self.dump('  Bypassing section (base: 0x%x, size: 0x%x)' % (addr, size))



  def gen_stim_header_32(self, stim_file):

    self.__parse_binaries(4)

    self.__gen_stim_header(stim_file, 4)

  def gen_stim_slm_64(self, stim_file):

    self.__parse_binaries(8)

    self.__gen_stim_slm(stim_file, 8)


  def gen_stim_bin(self, stim_file):

    self.__parse_binaries(1)

    try:
      os.makedirs(os.path.dirname(stim_file))
    except:
      pass

    with open(stim_file, 'wb') as file:
      prev_addr = None
      for key in sorted(self.mem.keys()):
        addr = int(key)
        if prev_addr is not None:
          while prev_addr != addr - 1:
            file.write(struct.pack('B', 0))
            prev_addr += 1

        prev_addr = addr
        file.write(struct.pack('B', int(self.mem.get(key))))



class Efuse(object):

  def __init__(self, config, verbose=False):
    self.config = config
    self.verbose = verbose

    self.dump('Created efuse stimuli generator')


  def dump(self, str):
    if self.verbose:
      print (str)

  def gen_stim_txt(self, filename):


    user_efuses = {}

    efuses = self.config.get('**/efuse/values')
    if efuses is None:
      efuses = []
    else:
      efuses = efuses.get_dict()
      for efuse in efuses:
        efuse_id, val = efuse.split(':')
        efuse_id = int(efuse_id, 0)
        val = int(val, 0)
        user_efuses[efuse_id] = val

    nb_regs = self.config.get_child_int('**/efuse/nb_regs')

    pulp_chip = self.config.get_child_str('**/chip/name')

    pulp_chip_family = self.config.get_child_str('**/chip/pulp_chip_family')

    if pulp_chip_family == 'gap' or pulp_chip == 'vega' or pulp_chip == 'gap9':

      load_mode = self.config.get_child_str('**/runner/boot-mode')
      encrypted = self.config.get_child_str('**/efuse/encrypted')
      aes_key = self.config.get_child_str('**/efuse/aes_key')
      aes_iv = self.config.get_child_str('**/efuse/aes_iv')
      xtal_check = self.config.get_child_bool('**/efuse/xtal_check')
      xtal_check_delta = self.config.get_child_bool('**/efuse/xtal_check_delta')
      xtal_check_min = self.config.get_child_bool('**/efuse/xtal_check_min')
      xtal_check_max = self.config.get_child_bool('**/efuse/xtal_check_max')
      no_preload = self.config.get_child_str('**/efuse/no-preload')

      # In case we boot with the classic rom mode, don't init any efuse, the boot loader will boot with the default mode
      load_mode_hex = None

      if pulp_chip == 'gap':

        if load_mode == 'rom':
          load_mode_hex = 0x3A
        elif load_mode == 'spi':
          load_mode_hex = 0x0A
        elif load_mode == 'jtag':
          load_mode_hex = 0x12
        elif load_mode == 'rom_hyper':
          load_mode_hex = 0x2A
        elif load_mode == 'rom_spim_single':
          load_mode_hex = 0x32
        elif load_mode == 'rom_spim':
          load_mode_hex = 0x3A
        elif load_mode == 'jtag_dev' or load_mode == 'spi_dev':
          load_mode_hex = None

        if xtal_check:
            if load_mode_hex == None: load_mode_hex = 0
            load_mode_hex |= 1<<7
            delta = int(xtal_check_delta*((1 << 15)-1))
            efuses.append('26:0x%x' % (delta & 0xff))
            efuses.append('27:0x%x' % ((delta >> 8) & 0xff))
            efuses.append('28:0x%x' % (xtal_check_min))
            efuses.append('29:0x%x' % (xtal_check_max))

        if load_mode_hex != None:
            if encrypted: 
                load_mode_hex |= 0x40
                for i in range(0, 16):
                    efuses.append('%d:0x%s' % (2+i, aes_key[30-i*2:32-i*2]))
                for i in range(0, 8):
                    efuses.append('%d:0x%s' % (18+i, aes_iv[14-i*2:16-i*2]))

            efuses.append('0:%s' % load_mode_hex)
    
      elif pulp_chip == 'vega' or pulp_chip == 'gap9':
        efuses = [0] * 128
        info2 = 0
        info3 = 0
        info4 = 0
        info5 = 0
        info6 = 0

        clk_div = self.config.get_child_int('**/efuse/clkdiv')
        fll_freq = self.config.get_child_int('**/efuse/fll/freq')
        fll_assert_cycles = self.config.get_child_int('**/efuse/fll/assert_cycles')
        fll_lock_tolerance = self.config.get_child_int('**/efuse/fll/lock_tolerance')
        hyper_delay = self.config.get_child_int('**/efuse/hyper/delay')
        hyper_latency = self.config.get_child_int('**/efuse/hyper/latency')

        if load_mode == 'rom':
          # RTL platform | flash boot | no encryption | no wait xtal
          load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
        elif load_mode == 'rom_hyper':
          # RTL platform | flash boot | no encryption | no wait xtal
          load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
          # Hyperflash type
          info3 = (1 << 0)
        elif load_mode == 'rom_spim':
          # RTL platform | flash boot | no encryption | no wait xtal
          load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
          # SPI flash type
          info3 = (0 << 0)
        elif load_mode == 'rom_mram':
          # RTL platform | flash boot | no encryption | no wait xtal
          load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
          # MRAM type
          info3 = (2 << 0)
          # Activate MRAM TRIM CFG and fill it with dummy numbers until we get the real one. Also activate clock divider
          info6 |= (1 << 6) | (1<<7)
          info2 |= (2 << 3)
          efuses[56] = 32*4
          for i in range(0, 32):
            efuses [57+i] = i | ((i*4+1)<<8) | ((i*4+2)<<16) | ((i*4+3)<<24)
        
        if clk_div is not None:
          info6 |= 1 << 7
          info2 = (info2 & ~(3<<3)) | (clk_div << 3)


        if fll_freq is not None:
          info2 |= (1 << 0) | (1 << 2)
          efuses[31] = fll_freq

        if fll_lock_tolerance is not None or fll_assert_cycles is not None:
          info2 |= (1<< 1)
          efuses[32] = fll_lock_tolerance
          efuses[33] = fll_assert_cycles

        if hyper_delay is not None:
          info5 |= (1<<6)
          efuses[30] = hyper_delay

        if hyper_latency is not None:
          info5 |= (1<<7)
          efuses[51] = hyper_latency



        if load_mode_hex != None:
            if encrypted: 
                load_mode_hex |= 0x40
                info6 |= 1<<4
                for i in range(0, 16):
                    efuses[2+i] = aes_key[30-i*2:32-i*2]
                for i in range(0, 8):
                    efuses[18+i] = aes_iv[14-i*2:16-i*2]

            efuses[0] = load_mode_hex
    
        efuses[1] = info2
        efuses[37] = info3
        efuses[38] = info4
        efuses[39] = info5 
        efuses[40] = info6
      elif pulp_chip == 'gap_rev1':
          info3 = 0
          info6 = 0
          if load_mode == 'rom':
            # RTL platform | flash boot | no encryption | no wait xtal
            load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
          elif load_mode == 'rom_hyper':
            # RTL platform | flash boot | no encryption | no wait xtal
            load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
            # Hyperflash type
            info3 = (1 << 0)
          elif load_mode == 'rom_spim':
            # RTL platform | flash boot | no encryption | no wait xtal
            load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
            # SPI flash type
            info3 = (0 << 0)
          
          if xtal_check:
              if load_mode_hex == None: load_mode_hex = 0
              load_mode_hex |= 1<<7
              delta = int(xtal_check_delta*((1 << 15)-1))
              efuses.append('26:0x%x' % (delta & 0xff))
              efuses.append('27:0x%x' % ((delta >> 8) & 0xff))
              efuses.append('28:0x%x' % (xtal_check_min))
              efuses.append('29:0x%x' % (xtal_check_max))

          if load_mode_hex != None:
              if encrypted: 
                  load_mode_hex |= 0x40
                  info6 |= 1<<4
                  for i in range(0, 16):
                      efuses.append('%d:0x%s' % (2+i, aes_key[30-i*2:32-i*2]))
                  for i in range(0, 8):
                      efuses.append('%d:0x%s' % (18+i, aes_iv[14-i*2:16-i*2]))

              efuses.append('0:%s' % load_mode_hex)
      
          efuses.append('1:%s' % 0)
          efuses.append('37:%s' % (info3))
          efuses.append('38:%s' % 0)
          efuses.append('39:%s' % 0)        
          efuses.append('40:%s' % (info6))
                  
      elif pulp_chip == 'gap8_revc':

          fll_freq = self.config.get_child_int('**/efuse/fll/freq')
          ref_clk_wait = self.config.get_child_int('**/efuse/ref_clk_wait')
          burst_size = self.config.get_child_int('**/efuse/burst_size')
          flash_id = self.config.get_child_bool('**/efuse/flash_id')
          fll_assert_cycles = self.config.get_child_int('**/efuse/fll/assert_cycles')
          fll_lock_tolerance = self.config.get_child_int('**/efuse/fll/lock_tolerance')
          hyper_delay = self.config.get_child_int('**/efuse/hyper/delay')
          hyper_latency = self.config.get_child_int('**/efuse/hyper/latency')

          if hyper_delay is None:
            hyper_delay = 3

          efuses = [0] * 128
          info3 = 0
          info2 = 0
          info6 = 0
          info5 = 0

          if self.config.get_child_str('**/vsim/model') == 'rtl':
            info7 = 1 # Don't use UDMA MEMCPY as it makes RTL platform crash
          else:
            info7 = 0
          if load_mode == 'rom':
            # RTL platform | flash boot | no encryption | no wait xtal
            load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
          elif load_mode == 'rom_hyper':
            # RTL platform | flash boot | no encryption | no wait xtal
            load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
            # Hyperflash type
            info3 = (1 << 0)
            info7 |= (1 << 2) # Partially reconfigure pads to overcome HW issue with rwds cg latch
          elif load_mode == 'rom_spim':
            # RTL platform | flash boot | no encryption | no wait xtal
            load_mode_hex = 2 | (2 << 3) | (0 << 4) | (0 << 5) | (0 << 6) | (0 << 7)
            # SPI flash type
            info3 = (0 << 0)
          
          if burst_size is not None:
            info6 |= (1 << 7)
            efuses[61] = burst_size & 0xff
            efuses[62] = (burst_size >> 8) & 0xff

          if flash_id:
            info6 |= (1 << 5)

          if fll_freq is not None:
            info2 |= (1 << 0)
            efuses[57] = fll_freq

          if ref_clk_wait is not None:
            info2 |= (1 << 6)
            efuses[35] = ref_clk_wait & 0xff
            efuses[36] = (ref_clk_wait >> 8) & 0xff
          else:
            info2 |= (1 << 6)
            efuses[35] = 0
            efuses[36] = 0

          if hyper_delay is not None:
            info5 |= (1<<6)
            efuses[32] |= hyper_delay

          if hyper_latency is not None:
            info5 |= (1<<7)
            efuses[51] |= hyper_latency


          if fll_lock_tolerance is not None or fll_assert_cycles is not None:
            info2 |= (1<< 1)
            efuses[58] = fll_lock_tolerance
            efuses[59] = fll_assert_cycles

          if xtal_check:
              if load_mode_hex == None: load_mode_hex = 0
              load_mode_hex |= 1<<7
              delta = int(xtal_check_delta*((1 << 15)-1))
              efuses[26] = delta & 0xff
              efuses[27] = (delta >> 8) & 0xff
              efuses[28] = xtal_check_min & 0xff
              efuses[29] = (xtal_check_min >> 8) & 0xff
              efuses[30] |= xtal_check_max & 0xff
              efuses[31] = (xtal_check_max >> 8) & 0xff

          if load_mode_hex != None:
              if encrypted: 
                  load_mode_hex |= 0x40
                  info6 |= 1<<4
                  for i in range(0, 16):
                      efuses[2+i] = int('0x%s' % aes_key[30-i*2:32-i*2], 0)
                  for i in range(0, 8):
                      efuses[18+i] = int('0x%s' % aes_iv[14-i*2:16-i*2], 0)

              efuses[0] = load_mode_hex
      
          efuses[1] = info2
          efuses[37] = info3
          efuses[38] = 0
          efuses[39] = info5    
          efuses[40] = info6
          efuses[60] = info7
                  

    # Efuse preloading file generation
    if pulp_chip == 'vega' or pulp_chip == 'gap9':

      self.dump('  Generating to file: ' + filename)

      with open(filename, 'w') as file:
        if no_preload is None or no_preload == False:
          for efuseId in range (0, 128):
              value = efuses[efuseId]
              self.dump('  Writing register (index: %d, value: 0x%x)' % (efuseId, value))
              file.write('{0:032b}\n'.format(value))
  
    elif pulp_chip == 'gap8_revc':

      values = [0] * nb_regs * 8
      for efuseId in range (0, nb_regs):
        value = user_efuses.get(efuseId)
        if value is None:
          value = efuses[efuseId]
        self.dump('  Writing register (index: %d, value: 0x%x)' % (efuseId, value))
        for index in range(0, 8):
            if (value >> index) & 1 == 1: values[efuseId + index*128] = 1

      self.dump('  Generating to file: ' + filename)

      with open(filename, 'w') as file:
          for value in values:
              file.write('%d ' % (value))

    else:

      values = [0] * nb_regs * 8
      for efuse in efuses:
          efuseId, value = efuse.split(':')
          self.dump('  Writing register (index: %d, value: 0x%x)' % (int(efuseId, 0), int(value, 0)))
          efuseId = int(efuseId, 0)
          value = int(value, 0)
          for index in range(0, 8):
              if (value >> index) & 1 == 1: values[efuseId + index*128] = 1

      self.dump('  Generating to file: ' + filename)

      with open(filename, 'w') as file:
          for value in values:
              file.write('%d ' % (value))

if __name__ == "__main__":
  parser = argparse.ArgumentParser(description='Generate stimuli')

  parser.add_argument("--binary", dest="binary", default=None, help="Specify input binary")
  parser.add_argument("--vectors", dest="vectors", default=None, help="Specify output vectors file")

  args = parser.parse_args()

  if args.binary is None:
    raise Exception('Specify the input binary with --binary=<path>')

  if args.vectors is not None:

    stim_gen = stim(verbose=True)

    stim_gen.add_binary(args.binary)

    stim_gen.gen_stim_header_32(args.vectors)

