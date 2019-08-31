// Copyright 2016 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#ifndef SECURITY_UTIL_LITE_UTIL_H_
#define SECURITY_UTIL_LITE_UTIL_H_

#include <stddef.h>

/* An implementation of memset that ought not to be optimized away;
 * useful for scrubbing security sensitive buffers. */
void *always_memset(void *s, int c, size_t n);

#endif  // SECURITY_UTIL_LITE_UTIL_H_
