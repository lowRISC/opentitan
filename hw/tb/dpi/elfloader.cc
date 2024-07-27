// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Modified version of the RISC-V Frontend Server
// (https://github.com/riscvarchive/riscv-fesvr, e41cfc3001293b5625c25412bd9b26e6e4ab8f7e)
//
// Nicole Narr <narrn@student.ethz.ch>
// Christopher Reinwardt <creinwar@student.ethz.ch>

#include <svdpi.h>
#include <cstring>
#include <string>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <map>
#include <iostream>
#include <stdint.h>

#define IS_ELF(hdr) \
  ((hdr).e_ident[0] == 0x7f && (hdr).e_ident[1] == 'E' && \
   (hdr).e_ident[2] == 'L'  && (hdr).e_ident[3] == 'F')

#define IS_ELF32(hdr) (IS_ELF(hdr) && (hdr).e_ident[4] == 1)
#define IS_ELF64(hdr) (IS_ELF(hdr) && (hdr).e_ident[4] == 2)

#define PT_LOAD 1
#define SHT_NOBITS 8
#define SHT_PROGBITS 0x1
#define SHT_GROUP 0x11

typedef struct {
  uint8_t  e_ident[16];
  uint16_t e_type;
  uint16_t e_machine;
  uint32_t e_version;
  uint32_t e_entry;
  uint32_t e_phoff;
  uint32_t e_shoff;
  uint32_t e_flags;
  uint16_t e_ehsize;
  uint16_t e_phentsize;
  uint16_t e_phnum;
  uint16_t e_shentsize;
  uint16_t e_shnum;
  uint16_t e_shstrndx;
} Elf32_Ehdr;

typedef struct {
  uint32_t sh_name;
  uint32_t sh_type;
  uint32_t sh_flags;
  uint32_t sh_addr;
  uint32_t sh_offset;
  uint32_t sh_size;
  uint32_t sh_link;
  uint32_t sh_info;
  uint32_t sh_addralign;
  uint32_t sh_entsize;
} Elf32_Shdr;

typedef struct
{
  uint32_t p_type;
  uint32_t p_offset;
  uint32_t p_vaddr;
  uint32_t p_paddr;
  uint32_t p_filesz;
  uint32_t p_memsz;
  uint32_t p_flags;
  uint32_t p_align;
} Elf32_Phdr;

typedef struct
{
  uint32_t st_name;
  uint32_t st_value;
  uint32_t st_size;
  uint8_t  st_info;
  uint8_t  st_other;
  uint16_t st_shndx;
} Elf32_Sym;

typedef struct {
  uint8_t  e_ident[16];
  uint16_t e_type;
  uint16_t e_machine;
  uint32_t e_version;
  uint64_t e_entry;
  uint64_t e_phoff;
  uint64_t e_shoff;
  uint32_t e_flags;
  uint16_t e_ehsize;
  uint16_t e_phentsize;
  uint16_t e_phnum;
  uint16_t e_shentsize;
  uint16_t e_shnum;
  uint16_t e_shstrndx;
} Elf64_Ehdr;

typedef struct {
  uint32_t sh_name;
  uint32_t sh_type;
  uint64_t sh_flags;
  uint64_t sh_addr;
  uint64_t sh_offset;
  uint64_t sh_size;
  uint32_t sh_link;
  uint32_t sh_info;
  uint64_t sh_addralign;
  uint64_t sh_entsize;
} Elf64_Shdr;

typedef struct {
  uint32_t p_type;
  uint32_t p_flags;
  uint64_t p_offset;
  uint64_t p_vaddr;
  uint64_t p_paddr;
  uint64_t p_filesz;
  uint64_t p_memsz;
  uint64_t p_align;
} Elf64_Phdr;

typedef struct {
  uint32_t st_name;
  uint8_t  st_info;
  uint8_t  st_other;
  uint16_t st_shndx;
  uint64_t st_value;
  uint64_t st_size;
} Elf64_Sym;

// address and size
std::vector<std::pair<uint64_t, uint64_t>> sections;

// memory based address and content
std::map<uint64_t, std::vector<uint8_t>> mems;

// Entrypoint
uint64_t entry = 0;
int section_index = 0;

extern "C" {
  char get_entry(long long *entry_ret);
  char get_section(long long *address_ret, long long *len_ret);
  char read_section(long long address, const svOpenArrayHandle buffer, long long len);
  char read_elf(const char *filename);
}

static void write (uint64_t address, uint64_t len, uint8_t *buf)
{
  std::vector<uint8_t> mem;
  for (int i = 0; i < len; i++) {
    mem.push_back(buf[i]);
  }
  mems.insert(std::make_pair(address, mem));
}

// Return the entry point reported by the ELF file
// Must be called after reading the elf file obviously
extern "C" char get_entry(long long *entry_ret)
{
  *entry_ret = entry;
  return 0;
}

// Iterator over the section addresses and lengths
// Returns:
// 0 if there are no more sections
// 1 if there are more sections to load
extern "C" char get_section(long long *address_ret, long long *len_ret)
{
  if (section_index < sections.size()) {
    *address_ret = sections[section_index].first;
    *len_ret = sections[section_index].second;
    section_index++;
    return 1;
  } else {
    return 0;
  }
}

extern "C" char read_section(long long address, const svOpenArrayHandle buffer, long long len)
{
  // get actual pointer
  char *buf = (char *) svGetArrayPtr(buffer);

  // check that the address points to a section
  if (!mems.count(address)) {
    printf("[ELF] ERROR: No section found for address %p\n", address);
    return -1;
  }

  // copy array
  long long int len_tmp = len;
  for (auto &datum : mems.find(address)->second) {
    if(len_tmp-- == 0){
      printf("[ELF] ERROR: Copied 0x%lx bytes. Buffer is full but there is still data available.\n", len);
      return -1;
    }

    *buf++ = datum;
  }

  return 0;
}

template <class E, class P, class Sh, class Sy>
static void load_elf(char *buf, size_t size)
{
  E  *eh = (E *)   buf;
  P  *ph = (P *)  (buf + eh->e_phoff);
  Sh *sh = (Sh *) (buf + eh->e_shoff);

  char *shstrtab = NULL;

  if(size < eh->e_phoff + (eh->e_phnum * sizeof(P))){
    printf("[ELF] ERROR: Filesize is smaller than advertised program headers (0x%lx vs 0x%lx)\n", size, eh->e_phoff + (eh->e_phnum * sizeof(P)));
    return;
  }

  entry = eh->e_entry;
  printf("[ELF] INFO: Entrypoint at %p\n", entry);

  // Iterate over all program header entries
  for (unsigned int i = 0; i < eh->e_phnum; i++) {
    // Check whether the current program header entry contains a loadable section of nonzero size
    if(ph[i].p_type == PT_LOAD && ph[i].p_memsz) {
      // Is this section something else than zeros?
      if (ph[i].p_filesz) {
        assert(size >= ph[i].p_offset + ph[i].p_filesz);
        sections.push_back(std::make_pair(ph[i].p_paddr, ph[i].p_memsz));
        write(ph[i].p_paddr, ph[i].p_filesz, (uint8_t*)buf + ph[i].p_offset);
      }

      if(ph[i].p_memsz > ph[i].p_filesz){
        printf("[ELF] WARNING: The section starting @ %p contains 0x%lx zero bytes which will NOT be preloaded!\n",
               ph[i].p_paddr, (ph[i].p_memsz - ph[i].p_filesz));
      }
    }
  }

  if(size < eh->e_shoff + (eh->e_shnum * sizeof(Sh))){
    printf("[ELF] ERROR: Filesize is smaller than advertised section headers (0x%lx vs 0x%lx)\n",
           size, eh->e_shoff + (eh->e_shnum * sizeof(Sh)));
    return;
  }

  if(eh->e_shstrndx >= eh->e_shnum){
    printf("[ELF] ERROR: Malformed ELF file. The index of the section header strings is out of bounds (0x%lx vs max 0x%lx)",
           eh->e_shstrndx, eh->e_shnum);
    return;
  }

  if(size < sh[eh->e_shstrndx].sh_offset + sh[eh->e_shstrndx].sh_size){
    printf("[ELF] ERROR: Filesize is smaller than advertised size of section name table (0x%lx vs 0x%lx)\n",
           size, sh[eh->e_shstrndx].sh_offset + sh[eh->e_shstrndx].sh_size);
    return;
  }

  // Get a direct pointer to the section name section
  shstrtab = buf + sh[eh->e_shstrndx].sh_offset;
  unsigned int strtabidx = 0, symtabidx = 0;

  // Iterate over all section headers to find .strtab and .symtab
  for (unsigned int i = 0; i < eh->e_shnum; i++) {
    // Get an upper limit on how long the name can be (length of the section name section minus the offset of the name)
    unsigned int max_len = sh[eh->e_shstrndx].sh_size - sh[i].sh_name;

    // Is this the string table?
    if(strcmp(shstrtab + sh[i].sh_name, ".strtab") == 0){
      printf("[ELF] INFO: Found string table at offset 0x%lx\n", sh[i].sh_offset);
      strtabidx = i;
      continue;
    }

    // Is this the symbol table?
    if(strcmp(shstrtab + sh[i].sh_name, ".symtab") == 0){
      printf("[ELF] INFO: Found symbol table at offset 0x%lx\n", sh[i].sh_offset);
      symtabidx = i;
      continue;
    }
  }
}

extern "C" char read_elf(const char *filename)
{
  char *buf = NULL;
  Elf64_Ehdr* eh64 = NULL;
  int fd = open(filename, O_RDONLY);
  char retval = 0;
  struct stat s;
  size_t size = 0;

  if(fd == -1){
    printf("[ELF] ERROR: Unable to open file %s\n", filename);
    retval = -1;
    goto exit;
  }

  if(fstat(fd, &s) < 0) {
    printf("[ELF] ERROR: Unable to read stats for file %s\n", filename);
    retval = -1;
    goto exit_fd;
  }

  size = s.st_size;

  if(size < sizeof(Elf64_Ehdr)){
    printf("[ELF] ERROR: File %s is too small to contain a valid ELF header (0x%lx vs 0x%lx)\n", filename, size, sizeof(Elf64_Ehdr));
    retval = -1;
    goto exit_fd;
  }

  buf = (char *) mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
  if(buf == MAP_FAILED){
    printf("[ELF] ERROR: Unable to memory map file %s\n", filename);
    retval = -1;
    goto exit_fd;
  }

  printf("[ELF] INFO: File %s was memory mapped to %p\n", filename, buf);

  eh64 = (Elf64_Ehdr *) buf;

  if(!(IS_ELF32(*eh64) || IS_ELF64(*eh64))){
    printf("[ELF] ERROR: File %s does not contain a valid ELF signature\n", filename);
    retval = -1;
    goto exit_mmap;
  }

  if (IS_ELF32(*eh64)){
    load_elf<Elf32_Ehdr, Elf32_Phdr, Elf32_Shdr, Elf32_Sym>(buf, size);
  } else {
    load_elf<Elf64_Ehdr, Elf64_Phdr, Elf64_Shdr, Elf64_Sym>(buf, size);
  }

exit_mmap:
  munmap(buf, size);

exit_fd:
  close(fd);

exit:
  return retval;
}
