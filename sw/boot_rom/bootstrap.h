#ifndef _F_BOOTSTRAP_H__
#define _F_BOOTSTRAP_H__

#include "sw/boot_rom/bootstrap_msgs.h"

/**
 * Bootstrap Flash with payload received on SPI device.
 *
 * The payload is expected to be split into frames as defined in
 * bootstrap_msgs.h. Frames are processed in consecutive number, with
 * |frame_num| in frame_hdr_t expected to increase monotonically.
 *
 * The last frame must be ord with FRAME_EOF_MARKER to signal the end of
 * payload transmission.
 *
 * @return Bootstrap status code.
 */
int bootstrap(void);

#endif  // _F_BOOTSTRAP_H__
