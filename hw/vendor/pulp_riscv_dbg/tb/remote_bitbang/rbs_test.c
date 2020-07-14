/* Copyright (C) 2020 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 *
 * Author: Robert Balas (balasr@iis.ee.ethz.ch)
 */

#include <stdio.h>
#include "remote_bitbang.h"

int main()
{
    unsigned char jtag_TCK, jtag_TMS, jtag_TDI, jtag_TRSTn;
    unsigned char jtag_TDO = 0;

    printf("calling rbs_init\n");
    int v = rbs_init(0);

    printf("tick 1\n");
    rbs_tick(&jtag_TCK, &jtag_TMS, &jtag_TDI, &jtag_TRSTn, jtag_TDO);
    printf("jtag exit is %d\n", rbs_done());
    return 0;
}
