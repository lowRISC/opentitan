// See LICENSE.Berkeley for license details.

#ifndef REMOTE_BITBANG_H
#define REMOTE_BITBANG_H

#include <stdint.h>
#include <sys/types.h>

#define VERBOSE 0

extern int rbs_err;

extern unsigned char tck;
extern unsigned char tms;
extern unsigned char tdi;
extern unsigned char trstn;
extern unsigned char tdo;
extern unsigned char quit;

extern int socket_fd;
extern int client_fd;

//static const ssize_t buf_size = 64 * 1024;
extern char recv_buf[64 * 1024];
extern ssize_t recv_start, recv_end;

// Create a new server, listening for connections from localhost on the given
// port.
int rbs_init(uint16_t port);

// Do a bit of work.
void rbs_tick(unsigned char *jtag_tck, unsigned char *jtag_tms,
              unsigned char *jtag_tdi, unsigned char *jtag_trstn,
              unsigned char jtag_tdo);

unsigned char rbs_done();

int rbs_exit_code();

// Check for a client connecting, and accept if there is one.
void rbs_accept();
// Execute any commands the client has for us.
// But we only execute 1 because we need time for the
// simulation to run.
void rbs_execute_command();

void rbs_reset(); //Assert TRST
void rbs_set(); //Deassert TRST

void rbs_set_pins(char _tck, char _tms, char _tdi);

#endif
