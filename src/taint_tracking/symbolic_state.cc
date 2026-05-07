// Copyright 2024 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license.
//
// [Minnie] Concolic execution engine implementation (paper III-D).
// See src/taint_tracking/symbolic_state.h for the interface.

#include "src/taint_tracking/symbolic_state.h"

#include <cstring>
#include <sstream>

#include "include/v8.h"
#include "src/handles/handles.h"
#include "src/objects/string-inl.h"
#include "src/taint_tracking.h"

#ifdef V8_TAINT_TRACKING_INCLUDE_CONCOLIC
#include <z3++.h>
#endif

namespace tainttracking {

namespace {

// Read the concrete byte sequence of `str`. For two-byte strings we
// truncate each code unit to its low byte - sufficient for ASCII-ish
// miniapp comparisons (phone numbers, IDs, URLs).
std::string ReadConcrete(v8::internal::String str) {
  std::string out;
  int len = str.length();
  out.resize(len);
  v8::internal::DisallowHeapAllocation no_gc;
  for (int i = 0; i < len; i++) {
    out[i] = static_cast<char>(str.Get(i) & 0xFF);
  }
  return out;
}

}  // namespace

bool IsSymbolic(v8::internal::String str) {
  v8::internal::DisallowHeapAllocation no_gc;
  int len = str.length();
  if (len == 0) return false;
  v8::internal::TaintData* chars = nullptr;
  if (str.IsSeqOneByteString()) {
    chars = v8::internal::SeqOneByteString::cast(str).GetTaintChars(no_gc);
  } else if (str.IsSeqTwoByteString()) {
    chars = v8::internal::SeqTwoByteString::cast(str).GetTaintChars(no_gc);
  } else {
    // External / cons / sliced: without flattening we can't cheaply
    // inspect the shadow. Fall back to false; the caller will treat
    // the value as concrete.
    return false;
  }
  if (chars == nullptr) return false;
  for (int i = 0; i < len; i++) {
    if (chars[i] & v8::TaintType::SYMBOLIC_MASK) return true;
  }
  return false;
}

void ReadSymbolicMask(v8::internal::String str, std::vector<uint8_t>* out) {
  v8::internal::DisallowHeapAllocation no_gc;
  int len = str.length();
  out->assign(len, 0);
  v8::internal::TaintData* chars = nullptr;
  if (str.IsSeqOneByteString()) {
    chars = v8::internal::SeqOneByteString::cast(str).GetTaintChars(no_gc);
  } else if (str.IsSeqTwoByteString()) {
    chars = v8::internal::SeqTwoByteString::cast(str).GetTaintChars(no_gc);
  }
  if (chars == nullptr) return;
  for (int i = 0; i < len; i++) {
    (*out)[i] = (chars[i] & v8::TaintType::SYMBOLIC_MASK) ? 1 : 0;
  }
}

// Paper III-D describes building SMT-LIB expressions of the form:
//
//   (= (str.++ <byte0> <byte1> ...) "concrete-rhs")
//
// where each symbolic byte of LHS becomes a fresh 1-char variable
// and each concrete byte becomes a 1-char string literal. Same shape
// for prefix (str.prefixof) and contains (str.contains).
std::string EmitSmtLib(const BranchConstraint& c) {
  std::ostringstream out;
  out << "(set-logic QF_S)\n";

  auto emit_side = [&](const std::string& label,
                       const std::string& concrete,
                       const std::vector<uint8_t>& sym) {
    for (size_t i = 0; i < concrete.size(); i++) {
      if (i < sym.size() && sym[i]) {
        out << "(declare-const " << label << "_b" << i << " String)\n";
      }
    }
    out << "(define-fun " << label << " () String (str.++";
    for (size_t i = 0; i < concrete.size(); i++) {
      out << ' ';
      if (i < sym.size() && sym[i]) {
        out << label << "_b" << i;
      } else {
        out << "\"";
        char ch = concrete[i];
        if (ch == '"' || ch == '\\') out << '\\';
        out << ch << "\"";
      }
    }
    if (concrete.empty()) {
      out << " \"\"";
    }
    out << "))\n";
  };

  emit_side("lhs", c.lhs_concrete, c.lhs_symbolic);
  emit_side("rhs", c.rhs_concrete, c.rhs_symbolic);

  switch (c.op) {
    case 0:  // equality
      out << "(assert (= lhs rhs))\n";
      break;
    case 1:  // startsWith
      out << "(assert (str.prefixof rhs lhs))\n";
      break;
    case 2:  // includes
      out << "(assert (str.contains lhs rhs))\n";
      break;
  }
  out << "(check-sat)\n(get-model)\n";
  return out.str();
}

ForkAssignment QueryFork(v8::internal::Isolate* isolate,
                         v8::internal::Handle<v8::internal::String> lhs,
                         v8::internal::Handle<v8::internal::String> rhs,
                         int op) {
  ForkAssignment result;
  (void)isolate;

  if (!IsSymbolic(*lhs) && !IsSymbolic(*rhs)) {
    // No symbolic bytes - nothing to fork on.
    return result;
  }

  BranchConstraint c;
  c.op = op;
  c.lhs_concrete = ReadConcrete(*lhs);
  c.rhs_concrete = ReadConcrete(*rhs);
  ReadSymbolicMask(*lhs, &c.lhs_symbolic);
  ReadSymbolicMask(*rhs, &c.rhs_symbolic);

#ifdef V8_TAINT_TRACKING_INCLUDE_CONCOLIC
  // Feed the constraint to Z3. We build the expression via the C++
  // API rather than string-parsing our own emitted script; EmitSmtLib
  // stays available for logging/tests.
  try {
    z3::context ctx;
    z3::solver solver(ctx);

    auto build_side = [&](const std::string& label,
                          const std::string& concrete,
                          const std::vector<uint8_t>& sym) -> z3::expr {
      z3::expr_vector parts(ctx);
      for (size_t i = 0; i < concrete.size(); i++) {
        if (i < sym.size() && sym[i]) {
          std::string name = label + "_b" + std::to_string(i);
          parts.push_back(ctx.string_const(name.c_str()));
        } else {
          parts.push_back(ctx.string_val(std::string(1, concrete[i])));
        }
      }
      if (parts.empty()) return ctx.string_val("");
      return z3::concat(parts);
    };

    z3::expr lhs_e = build_side("lhs", c.lhs_concrete, c.lhs_symbolic);
    z3::expr rhs_e = build_side("rhs", c.rhs_concrete, c.rhs_symbolic);

    // We want the fork to take the other branch. The concrete
    // execution already took the current branch, so assert the
    // negation of the current comparison outcome.
    bool currently_true = false;
    switch (op) {
      case 0: currently_true = (c.lhs_concrete == c.rhs_concrete); break;
      case 1: currently_true = (c.lhs_concrete.rfind(c.rhs_concrete, 0) == 0); break;
      case 2: currently_true = (c.lhs_concrete.find(c.rhs_concrete) != std::string::npos); break;
    }
    z3::expr comparison = ctx.bool_val(false);
    switch (op) {
      case 0: comparison = (lhs_e == rhs_e); break;
      case 1: comparison = z3::prefixof(rhs_e, lhs_e); break;
      case 2: comparison = z3::contains(lhs_e, rhs_e); break;
      default: return result;
    }
    solver.add(currently_true ? !comparison : comparison);

    if (solver.check() != z3::sat) {
      return result;
    }
    z3::model m = solver.get_model();

    auto extract_side = [&](const std::string& label,
                            const std::string& concrete,
                            const std::vector<uint8_t>& sym) -> std::string {
      std::string out = concrete;
      for (size_t i = 0; i < concrete.size(); i++) {
        if (i < sym.size() && sym[i]) {
          std::string name = label + "_b" + std::to_string(i);
          try {
            z3::expr v = m.eval(ctx.string_const(name.c_str()),
                                /*model_completion=*/true);
            std::string s = v.get_string();
            if (s.size() == 1) out[i] = s[0];
          } catch (...) {}
        }
      }
      return out;
    };

    result.available = true;
    result.lhs_assignment = extract_side("lhs", c.lhs_concrete, c.lhs_symbolic);
    result.rhs_assignment = extract_side("rhs", c.rhs_concrete, c.rhs_symbolic);
  } catch (const std::exception&) {
    // Z3 threw - give up quietly so the interpreter continues.
  }
#endif

  return result;
}

}  // namespace tainttracking
