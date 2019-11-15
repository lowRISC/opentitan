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
#ifndef SECURITY_UTIL_LITE_P256_ECDSA_H_
#define SECURITY_UTIL_LITE_P256_ECDSA_H_

// Using current directory as relative include path here since
// this code typically gets lifted into a variety of build systems
// and directory structures.
#include "cryptoc/p256.h"

#ifdef __cplusplus
extern "C" {
#endif

// {r,s} := {kG mod n, (message + r*key)/k mod n}
//
// Note: message is a p256_int.
// Convert from a binary string using p256_from_bin().
void p256_ecdsa_sign(const p256_int* key,
                     const p256_int* message,
                     p256_int* r, p256_int* s);

// Returns 0 if {r,s} is not a signature on message for
// public key {key_x,key_y}.
//
// Note: message is a p256_int.
// Convert from a binary string using p256_from_bin().
int p256_ecdsa_verify(const p256_int* key_x,
                      const p256_int* key_y,
                      const p256_int* message,
                      const p256_int* r, const p256_int* s);

#ifdef __cplusplus
}
#endif

#endif  // SECURITY_UTIL_LITE_P256_ECDSA_H_
