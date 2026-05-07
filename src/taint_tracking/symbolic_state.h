// Copyright 2024 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license.
//
// [Minnie] Concolic execution engine skeleton (paper III-D).
//
// When an interpreted bytecode (TestEqual / TestEqualStrict /
// JumpIfTrue / JumpIfFalse) compares a value whose shadow carries
// the SYMBOLIC_MASK bit, V8 calls into SymbolicState below. The
// engine records the current concrete value, builds an SMT-LIB
// query describing the branch condition from the symbolic bytes,
// and asks Z3 for an alternative assignment that would take the
// other branch. The alternative is returned to the caller, which
// queues a re-execution with the alternative input.
//
// When v8_taint_tracking_include_concolic=false, this module
// compiles to a stub - each entry point returns immediately so
// the interpreter hooks become cheap no-ops.

#ifndef V8_TAINT_TRACKING_SYMBOLIC_STATE_H_
#define V8_TAINT_TRACKING_SYMBOLIC_STATE_H_

#include <cstdint>
#include <string>
#include <vector>

#include "include/v8.h"

namespace v8 {
namespace internal {
class Isolate;
class String;
template <class T> class Handle;
}  // namespace internal
}  // namespace v8

namespace tainttracking {

// Result of inspecting a branch condition.
struct BranchConstraint {
  // Concrete byte sequence of the LHS string at the comparison site.
  std::string lhs_concrete;
  // Concrete byte sequence of the RHS string.
  std::string rhs_concrete;
  // Per-byte symbolic mask for each side (1 = symbolic, 0 = concrete).
  std::vector<uint8_t> lhs_symbolic;
  std::vector<uint8_t> rhs_symbolic;
  // Operator: 0 = equality, 1 = prefix, 2 = contains.
  int op;
};

// Alternative assignment the solver produced for an already-seen
// constraint. If `available` is false, the solver was unable to
// find an input (unsat / timeout / Z3 not linked). If `available`
// is true, `lhs_assignment` is the new concrete byte sequence that
// flips the branch direction; `rhs_assignment` is optional.
struct ForkAssignment {
  bool available = false;
  std::string lhs_assignment;
  std::string rhs_assignment;
};

// [Minnie] Main entry point. Called from the interpreter just
// before it dispatches a bytecode like TestEqual / JumpIfTrue on a
// string value that carries symbolic bytes.
//
// * `lhs`/`rhs`: the two operands as V8 strings. Either may be
//   symbolic; the engine reads the shadow bytes of each.
// * `op`: 0 eq, 1 startsWith, 2 includes.
//
// Returns a ForkAssignment that, if available, describes a new
// concrete value that would send the branch down the other path.
//
// When concolic support is not compiled in, returns an inert
// assignment (available=false) without touching Z3.
ForkAssignment QueryFork(v8::internal::Isolate* isolate,
                         v8::internal::Handle<v8::internal::String> lhs,
                         v8::internal::Handle<v8::internal::String> rhs,
                         int op);

// Lower-level helper that just builds an SMT-LIB representation of
// the given constraint (no solver invocation). Useful for tests and
// for callers that want to log the constraint without forking.
std::string EmitSmtLib(const BranchConstraint& c);

// Returns true iff `str` has at least one byte with SYMBOLIC_MASK
// set, meaning branches on `str` should be concolically explored.
bool IsSymbolic(v8::internal::String str);

// Reads the per-byte symbolic mask of `str` into `out`. `out` is
// resized to str->length().
void ReadSymbolicMask(v8::internal::String str, std::vector<uint8_t>* out);

}  // namespace tainttracking

#endif  // V8_TAINT_TRACKING_SYMBOLIC_STATE_H_
