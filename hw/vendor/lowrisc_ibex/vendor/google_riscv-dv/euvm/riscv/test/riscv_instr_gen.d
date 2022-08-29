/*
 * Copyright 2022 Coverify Systems Technology
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import uvm;
import esdl;

int main(string[] args) {
  import std.stdio: writeln;

  uint random_seed;
  uint thread_index;
  uint thread_count;

  CommandLine cmdl = new CommandLine(args);

  if (cmdl.plusArgs("random_seed=" ~ "%d", random_seed))
    writeln("Using random_seed: ", random_seed);
  else random_seed = 1;

  if (! cmdl.plusArgs("thread_index=" ~ "%d", thread_index))
    thread_index = 0;
  if (! cmdl.plusArgs("thread_count=" ~ "%d", thread_count))
    thread_count = 1;

  auto testbench = new uvm_testbench;

  testbench.multicore(thread_index, thread_count);
  testbench.elaborate("test", args);
  testbench.set_seed(random_seed);
  testbench.set_async_mode();

  return testbench.start();
}
