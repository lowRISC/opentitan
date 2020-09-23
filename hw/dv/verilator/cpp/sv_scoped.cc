// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sv_scoped.h"

#include <cassert>
#include <sstream>

// Set scope by name, returning the old scope. If the name doesn't describe a
// valid scope, throw an SVScoped::Error.
static svScope SetAbsScope(const std::string &name) {
  svScope new_scope = svGetScopeFromName(name.c_str());
  if (!new_scope)
    throw SVScoped::Error(name);
  return svSetScope(new_scope);
}

// Resolve name to a scope, using the rules described in the comment above the
// class in sv_scoped.h, and then set it. Returns the old scope.
static svScope SetRelScope(const std::string &name) {
  // Absolute (or empty) names resolve to themselves
  if (name[0] != '.') {
    return SetAbsScope(name);
  }

  svScope prev_scope = svGetScope();

  // Special case: If name is ".", it means to use the current scope. Rather
  // than changing scope, we can just return where we are going to stay.
  if (name == ".")
    return prev_scope;

  // For anything else, count how many dots appear after the first one (so
  // ..foo gives an up_count of 1; ...bar gives an up_count of 2).
  size_t first_not_dot = name.find_first_not_of('.', 1);
  if (first_not_dot == std::string::npos) {
    // name looks like "....": that's fine, it just means to go up some number
    // of steps from the current position and not down again. Amend
    // first_not_dot to point at the '\0'.
    first_not_dot = name.size();
  }
  size_t up_count = first_not_dot - 1;

  // Get the name of the current scope, so that we can perform surgery.
  std::string scope_name = svGetNameFromScope(prev_scope);

  // scope_name will look something like "TOP.foo.bar". Search up_count
  // dots from the end, setting last_dot to point at the last dot that should
  // appear in the resolved name.
  //
  // If up_count is too large, behave like "cd /; cd .." and stop at the
  // left-most dot.
  size_t last_dot = scope_name.size();
  for (size_t i = 0; i < up_count; ++i) {
    // This shouldn't ever trigger (because it would mean scope_name was
    // either empty or started with a "."), but allowing it makes the code a
    // bit more uniform.
    if (last_dot == 0)
      break;

    size_t dot = scope_name.rfind('.', last_dot - 1);
    if (dot == std::string::npos)
      break;

    last_dot = dot;
  }

  // Delete everything from last_dot onwards. If we are actually pointing at a
  // dot, this will do something like "TOP.foo.bar" -> "TOP.foo". If up_count
  // was zero or there were no dots, last_dot will equal the size of the string
  // (which means, conveniently, that erase is a no-op).
  scope_name.erase(last_dot);

  // If first_not_dot points inside name (so name looked like "..foo.bar"
  // rather than "..."), subtract one to point at the last dot of the initial
  // segment (we know there is one because name[0] == '.') and then append
  // everything to scope_name starting from there. For example, if scope_name
  // was "TOP.foo.bar.baz" and name was "..qux", we will have just amended
  // scope_name to be "TOP.foo.bar". Now we want to add ".qux".
  if (first_not_dot < name.size()) {
    scope_name.append(name, first_not_dot - 1, std::string::npos);
  }

  return SetAbsScope(scope_name);
}

SVScoped::SVScoped(const std::string &name) : prev_scope_(SetRelScope(name)) {}

SVScoped::Error::Error(const std::string &scope_name)
    : scope_name_(scope_name) {
  std::ostringstream oss;
  oss << "No such SystemVerilog scope: `" << scope_name << "'.";
  msg_ = oss.str();
}
